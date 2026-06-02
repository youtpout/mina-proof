/**
 * BenchHash.ts
 *
 * Benchmark 4 ZK programs using recursive proof merging:
 *   1. Poseidon   — native Mina/Pasta field hash
 *   2. SHA2-256   — Hash.SHA2_256
 *   3. Keccak256  — Hash.Keccak256
 *   4. Blake2b    — Hash.BLAKE2B
 *   5. ECDSA      — Ethereum EIP-191 signature verification on secp256k1
 *
 * Each program has two methods:
 *   base(elem)            → hash(elem)               produces first proof
 *   step(prevProof, elem) → hash(prevOutput || elem)  merges with previous
 *
 * The iteration loop is OUTSIDE the circuit:
 *   proof = base(inputs[0])
 *   proof = step(proof, inputs[1])
 *   proof = step(proof, inputs[2])
 *   ...
 *
 * publicOutput: Field  — carries the running hash state between proofs.
 * For byte-based hashes the digest (Bytes) is packed into a Field (31 bytes)
 * so it can travel as publicOutput, then unpacked in the next step.
 *
 * Run:
 *   npx ts-node src/BenchHash.ts
 */

import {
    Field,
    Poseidon,
    ZkProgram,
    SelfProof,
    Hash,
    Bytes,
    UInt8,
    Bool,
    Crypto,
    createForeignCurve,
    createEcdsa,
    Cache,
    setBackend,
} from "o1js";

const INPUT_SIZE = 3;

setBackend('native');

// ---------------------------------------------------------------------------
// Bytes types — sizes must be known at compile time outside ZkPrograms
// ---------------------------------------------------------------------------

class Bytes31 extends Bytes(31) { }  // one field element encoded
class Bytes62 extends Bytes(62) { }  // previous digest (31) + next element (31)
class Bytes32 extends Bytes(32) { }  // Ethereum signed message payload
class Bytes60 extends Bytes(60) { }  // EIP-191 prefix (26) + "32" + message (32)

class Secp256k1 extends createForeignCurve(Crypto.CurveParams.Secp256k1) { }
class Secp256k1Scalar extends Secp256k1.Scalar { }
class Ecdsa extends createEcdsa(Secp256k1) { }

// ---------------------------------------------------------------------------
// In-circuit helpers
// ---------------------------------------------------------------------------

/**
 * Encode a Field as 31 UInt8 bytes (little-endian bit decomposition, 248 bits).
 * Safe within the Pasta field (~254-bit capacity).
 */
function fieldToBytes31(f: Field): UInt8[] {
    const bits = f.toBits(248); // 248 = 31 × 8
    const result: UInt8[] = [];
    for (let b = 0; b < 31; b++) {
        let byte = Field(0);
        for (let bit = 0; bit < 8; bit++) {
            const bitField: Field = (bits[b * 8 + bit] as Bool).toField();
            byte = byte.add(bitField.mul(Field(1 << bit)));
        }
        result.push(UInt8.from(byte));
    }
    return result;
}

/**
 * Pack a digest (Bytes) into a Field by treating the first 31 bytes as a
 * big-endian integer.  Used to carry the running state as publicOutput.
 */
function digestToField(digest: Bytes): Field {
    let acc = Field(0);
    for (let i = 0; i < 31; i++) {
        // acc = acc * 256 + byte[i]
        acc = acc.mul(Field(256)).add(digest.bytes[i].value);
    }
    return acc;
}

// ---------------------------------------------------------------------------
// 1. Poseidon — publicOutput: Field (native, no packing needed)
// ---------------------------------------------------------------------------

const PoseidonProgram = ZkProgram({
    name: "PoseidonBench",
    publicOutput: Field,

    methods: {
        // First element: output = Poseidon(elem)
        base: {
            privateInputs: [Field],
            async method(elem: Field): Promise<{ publicOutput: Field }> {
                return { publicOutput: Poseidon.hash([elem]) };
            },
        },

        // Next elements: output = Poseidon(prevOutput, elem)
        step: {
            privateInputs: [SelfProof<undefined, Field>, Field],
            async method(
                prevProof: SelfProof<undefined, Field>,
                elem: Field
            ): Promise<{ publicOutput: Field }> {
                prevProof.verify();
                return {
                    publicOutput: Poseidon.hash([prevProof.publicOutput, elem]),
                };
            },
        },
    },
});

// ---------------------------------------------------------------------------
// 2. SHA2-256 — publicOutput: Field (digest packed to 31 bytes → Field)
// ---------------------------------------------------------------------------

const Sha256Program = ZkProgram({
    name: "Sha256Bench",
    publicOutput: Field,

    methods: {
        base: {
            privateInputs: [Field],
            async method(elem: Field): Promise<{ publicOutput: Field }> {
                const input = Bytes31.from(fieldToBytes31(elem));
                const digest = Hash.SHA2_256.hash(input);
                return { publicOutput: digestToField(digest) };
            },
        },

        step: {
            privateInputs: [SelfProof<undefined, Field>, Field],
            async method(
                prevProof: SelfProof<undefined, Field>,
                elem: Field
            ): Promise<{ publicOutput: Field }> {
                prevProof.verify();
                // Unpack previous output (Field → 31 bytes) and concat with new element
                const combined = Bytes62.from([
                    ...fieldToBytes31(prevProof.publicOutput),
                    ...fieldToBytes31(elem),
                ]);
                const digest = Hash.SHA2_256.hash(combined);
                return { publicOutput: digestToField(digest) };
            },
        },
    },
});

// ---------------------------------------------------------------------------
// 3. Keccak256 — same structure as SHA256
// ---------------------------------------------------------------------------

const Keccak256Program = ZkProgram({
    name: "Keccak256Bench",
    publicOutput: Field,

    methods: {
        base: {
            privateInputs: [Field],
            async method(elem: Field): Promise<{ publicOutput: Field }> {
                const input = Bytes31.from(fieldToBytes31(elem));
                const digest = Hash.Keccak256.hash(input);
                return { publicOutput: digestToField(digest) };
            },
        },

        step: {
            privateInputs: [SelfProof<undefined, Field>, Field],
            async method(
                prevProof: SelfProof<undefined, Field>,
                elem: Field
            ): Promise<{ publicOutput: Field }> {
                prevProof.verify();
                const combined = Bytes62.from([
                    ...fieldToBytes31(prevProof.publicOutput),
                    ...fieldToBytes31(elem),
                ]);
                const digest = Hash.Keccak256.hash(combined);
                return { publicOutput: digestToField(digest) };
            },
        },
    },
});

// ---------------------------------------------------------------------------
// 4. Blake2b — same structure
// ---------------------------------------------------------------------------

const Blake2bProgram = ZkProgram({
    name: "Blake2bBench",
    publicOutput: Field,

    methods: {
        base: {
            privateInputs: [Field],
            async method(elem: Field): Promise<{ publicOutput: Field }> {
                const input = Bytes31.from(fieldToBytes31(elem));
                const digest = Hash.BLAKE2B.hash(input);
                return { publicOutput: digestToField(digest) };
            },
        },

        step: {
            privateInputs: [SelfProof<undefined, Field>, Field],
            async method(
                prevProof: SelfProof<undefined, Field>,
                elem: Field
            ): Promise<{ publicOutput: Field }> {
                prevProof.verify();
                const combined = Bytes62.from([
                    ...fieldToBytes31(prevProof.publicOutput),
                    ...fieldToBytes31(elem),
                ]);
                const digest = Hash.BLAKE2B.hash(combined);
                return { publicOutput: digestToField(digest) };
            },
        },
    },
});

// ---------------------------------------------------------------------------
// 5. ECDSA Ethereum — secp256k1 + EIP-191 ("personal_sign" / ethers signMessage)
// ---------------------------------------------------------------------------

const EcdsaEthereumProgram = ZkProgram({
    name: "EcdsaEthereumBench",
    publicOutput: Bool,

    methods: {
        base: {
            privateInputs: [Bytes32, Ecdsa, Secp256k1],
            async method(
                message: Bytes32,
                signature: Ecdsa,
                publicKey: Secp256k1
            ): Promise<{ publicOutput: Bool }> {
                const isValid = signature.verifyEthers(message, publicKey);
                isValid.assertTrue("Ethereum ECDSA signature must verify");
                return { publicOutput: isValid };
            },
        },

        step: {
            privateInputs: [SelfProof<undefined, Bool>, Bytes32, Ecdsa, Secp256k1],
            async method(
                prevProof: SelfProof<undefined, Bool>,
                message: Bytes32,
                signature: Ecdsa,
                publicKey: Secp256k1
            ): Promise<{ publicOutput: Bool }> {
                prevProof.verify();
                prevProof.publicOutput.assertTrue("previous Ethereum ECDSA proof must verify");

                const isValid = signature.verifyEthers(message, publicKey);
                const merged = prevProof.publicOutput.and(isValid);
                merged.assertTrue("merged Ethereum ECDSA signatures must verify");
                return { publicOutput: merged };
            },
        },
    },
});

// ---------------------------------------------------------------------------
// Recursive fold — runs outside the circuit
//
//   proof = base(inputs[0])
//   for i in 1..N: proof = step(proof, inputs[i])
// ---------------------------------------------------------------------------

type AnyProgram = {
    base(elem: Field): Promise<{ proof: SelfProof<undefined, Field> }>;
    step(prev: SelfProof<undefined, Field>, elem: Field): Promise<{ proof: SelfProof<undefined, Field> }>;
};

async function recursiveFold(
    program: AnyProgram,
    inputs: Field[]
): Promise<SelfProof<undefined, Field>> {
    let { proof } = await program.base(inputs[0]);
    for (let i = 1; i < inputs.length; i++) {
        ({ proof } = await program.step(proof, inputs[i]));
    }
    return proof;
}

// ---------------------------------------------------------------------------
// Benchmark helpers
// ---------------------------------------------------------------------------

interface BenchResult {
    name: string;
    rowsBase: number;
    rowsStep: number;
    compileMs: number;
    proveMs: number; // total for all INPUT_SIZE steps
    verifyMs: number;
    totalMs: number;
}

type EthereumSignatureTrial = {
    message: Bytes32;
    signature: Ecdsa;
    publicKey: Secp256k1;
};

function separator(title: string) {
    console.log("\n" + "─".repeat(64));
    console.log(`  ${title}`);
    console.log("─".repeat(64));
}

async function runBench<P extends {
    analyzeMethods(): Promise<Record<string, { rows: number }>>;
    compile(): Promise<unknown>;
    verify(p: unknown): Promise<boolean>;
} & AnyProgram>(
    program: P,
    inputs: Field[],
    name: string
): Promise<BenchResult> {
    separator(`Benchmarking: ${name}`);

    const analysis = await program.analyzeMethods();
    const rowsBase = (analysis["base"] as { rows: number }).rows;
    const rowsStep = (analysis["step"] as { rows: number }).rows;
    console.log(`  Rows (base) : ${rowsBase.toLocaleString()}`);
    console.log(`  Rows (step) : ${rowsStep.toLocaleString()}`);

    const t0 = performance.now();
    await program.compile();
    const compileMs = Math.round(performance.now() - t0);
    console.log(`  Compile     : ${compileMs} ms`);

    const t1 = performance.now();
    const proof = await recursiveFold(program as AnyProgram, inputs);
    const proveMs = Math.round(performance.now() - t1);
    console.log(`  Prove total : ${proveMs} ms  (${inputs.length} recursive steps)`);
    console.log(`  Final hash  : ${proof.publicOutput.toString()}`);

    const t2 = performance.now();
    const ok = await program.verify(proof);
    const verifyMs = Math.round(performance.now() - t2);
    console.log(`  Verify      : ${verifyMs} ms  (valid=${ok})`);

    const totalMs = compileMs + proveMs + verifyMs;
    console.log(`  TOTAL       : ${totalMs} ms`);

    return { name, rowsBase, rowsStep, compileMs, proveMs, verifyMs, totalMs };
}

function ethereumPersonalMessageHash(message: Bytes32): Bytes {
    const prefix = Bytes.fromString("\x19Ethereum Signed Message:\n");
    const length = Bytes.fromString(String(message.length));

    return Hash.Keccak256.hash(
        Bytes60.from([
            ...prefix.bytes,
            ...length.bytes,
            ...message.bytes,
        ])
    );
}

function createEthereumSignatureTrials(count: number): EthereumSignatureTrial[] {
    return Array.from({ length: count }, (_, i) => {
        const privateKey = Secp256k1Scalar.random();
        const publicKey = Secp256k1.generator.scale(privateKey);
        const message = Bytes32.fromString(
            `eth ecdsa wallet benchmark #${String(i + 1).padStart(4, "0")}`
        );
        const signature = Ecdsa.signHash(
            ethereumPersonalMessageHash(message),
            privateKey.toBigInt()
        );

        return { message, signature, publicKey };
    });
}

async function recursiveEthereumEcdsaFold(
    trials: EthereumSignatureTrial[]
): Promise<SelfProof<undefined, Bool>> {
    let { proof } = await EcdsaEthereumProgram.base(
        trials[0].message,
        trials[0].signature,
        trials[0].publicKey
    );

    for (let i = 1; i < trials.length; i++) {
        ({ proof } = await EcdsaEthereumProgram.step(
            proof,
            trials[i].message,
            trials[i].signature,
            trials[i].publicKey
        ));
    }

    return proof;
}

async function runEthereumEcdsaBench(
    trials: EthereumSignatureTrial[]
): Promise<BenchResult> {
    const name = "ECDSA Ethereum";
    separator(`Benchmarking: ${name}`);

    const analysis = await EcdsaEthereumProgram.analyzeMethods();
    const rowsBase = (analysis["base"] as { rows: number }).rows;
    const rowsStep = (analysis["step"] as { rows: number }).rows;
    console.log(`  Rows (base) : ${rowsBase.toLocaleString()}`);
    console.log(`  Rows (step) : ${rowsStep.toLocaleString()}`);

    const t0 = performance.now();
    await EcdsaEthereumProgram.compile();
    const compileMs = Math.round(performance.now() - t0);
    console.log(`  Compile     : ${compileMs} ms`);

    const t1 = performance.now();
    const proof = await recursiveEthereumEcdsaFold(trials);
    const proveMs = Math.round(performance.now() - t1);
    console.log(`  Prove total : ${proveMs} ms  (${trials.length} recursive signature steps)`);
    console.log(`  Final valid : ${proof.publicOutput.toString()}`);

    const t2 = performance.now();
    const ok = await EcdsaEthereumProgram.verify(proof);
    const verifyMs = Math.round(performance.now() - t2);
    console.log(`  Verify      : ${verifyMs} ms  (valid=${ok})`);

    const totalMs = compileMs + proveMs + verifyMs;
    console.log(`  TOTAL       : ${totalMs} ms`);

    return { name, rowsBase, rowsStep, compileMs, proveMs, verifyMs, totalMs };
}

// ---------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------

async function main() {
    console.log("\n╔══════════════════════════════════════════════════════════════╗");
    console.log(`║  o1js Recursive Proof Benchmark — ${INPUT_SIZE} inputs               ║`);
    console.log("║  Loop is OUTSIDE the circuit (proof merging pattern)        ║");
    console.log("║  Poseidon / SHA2-256 / Keccak256 / Blake2b / ECDSA          ║");
    console.log("╚══════════════════════════════════════════════════════════════╝");

    const inputs: Field[] = Array.from({ length: INPUT_SIZE }, (_, i) =>
        Field(i + 1)
    );

    const results: BenchResult[] = [];

    results.push(await runEthereumEcdsaBench(
        createEthereumSignatureTrials(INPUT_SIZE)
    ));
    results.push(await runBench(PoseidonProgram, inputs, "Poseidon (native)"));
    results.push(await runBench(Sha256Program, inputs, "SHA2-256"));
    results.push(await runBench(Keccak256Program, inputs, "Keccak256"));
    results.push(await runBench(Blake2bProgram, inputs, "Blake2b"));


    // ── Summary ───────────────────────────────────────────────────────────────
    separator("Summary");

    const p = (s: string, n: number) => s.padEnd(n);
    const r = (s: string, n: number) => s.padStart(n);

    console.log(
        p("Hash", 20) +
        r("Base rows", 12) +
        r("Step rows", 12) +
        r("Compile(ms)", 14) +
        r("Prove(ms)", 16) +
        r("Verify(ms)", 13) +
        r("Total(ms)", 12)
    );
    console.log("─".repeat(99));

    const baseline = results[0].proveMs || 1;
    for (const res of results) {
        const mult = (res.proveMs / baseline).toFixed(1);
        console.log(
            p(res.name, 20) +
            r(res.rowsBase.toLocaleString(), 12) +
            r(res.rowsStep.toLocaleString(), 12) +
            r(res.compileMs.toString(), 14) +
            r(`${res.proveMs} (${mult}×)`, 16) +
            r(res.verifyMs.toString(), 13) +
            r(res.totalMs.toString(), 12)
        );
    }

    console.log(`\n  Hash benches: ${INPUT_SIZE} inputs — 1 base proof + ${INPUT_SIZE - 1} recursive step proof(s)`);
    console.log(`  ECDSA bench: ${INPUT_SIZE} Ethereum EIP-191 signatures — 1 base proof + ${INPUT_SIZE - 1} recursive step proof(s)`);
    console.log("  Step rows include SelfProof.verify() cost");
    console.log("  Prove ratio relative to Poseidon baseline (1×)\n");
}

main().catch((e) => {
    console.error(e);
    process.exit(1);
});
