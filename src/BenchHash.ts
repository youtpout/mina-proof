/**
 * BenchHash.ts
 *
 * Benchmark 4 ZK programs using different hash functions in o1js:
 *   1. Poseidon   — native Mina/Pasta field hash
 *   2. SHA2-256   — Hash.SHA2_256
 *   3. Keccak256  — Hash.Keccak256
 *   4. Blake2b    — Hash.BLAKE2B
 *
 * Each program receives 5 Field elements via Provable.Array(Field, 5).
 * The byte-based programs convert each Field to 31 bytes in-circuit.
 *
 * Iterative hashing pattern (same for all 4 programs):
 *   state = hash(elem[0])
 *   state = hash(state || elem[1])
 *   state = hash(state || elem[2])
 *   ...
 *
 * Run:
 *   npx ts-node src/BenchHash.ts
 */

import {
    Field,
    Poseidon,
    ZkProgram,
    Provable,
    Hash,
    Bytes,
    UInt8,
    Bool,
} from "o1js";

const INPUT_SIZE = 3;

// ---------------------------------------------------------------------------
// Field → 31 bytes (248 bits, safe for Pasta ~254-bit field)
// Used inside ZkPrograms to convert each Field element to bytes in-circuit
// ---------------------------------------------------------------------------

// Bytes types for the iterative steps:
//   - first step  : 31 bytes (one field element)
//   - later steps : 31 (digest truncated) + 31 (next field) = 62 bytes
class Bytes31 extends Bytes(31) { }
class Bytes62 extends Bytes(62) { }

/**
 * Convert a Field to 31 UInt8 bytes (big-endian, 248-bit).
 * Safe within the Pasta field (254-bit capacity).
 */
function fieldToBytes31(f: Field): UInt8[] {
    const bits = f.toBits(248); // 31 bytes × 8 bits
    const result: UInt8[] = [];
    for (let b = 0; b < 31; b++) {
        let byte = Field(0);
        for (let bit = 0; bit < 8; bit++) {
            // bits are little-endian from toBits()
            const bitField: Field = (bits[b * 8 + bit] as Bool).toField();
            byte = byte.add(bitField.mul(Field(1 << bit)));
        }
        result.push(UInt8.from(byte));
    }
    return result;
}

/**
 * Take the first 31 bytes of a digest (drop last byte to fit Bytes31).
 */
function digestTo31(digest: Bytes): UInt8[] {
    return digest.bytes.slice(0, 31);
}

// ---------------------------------------------------------------------------
// 1. Poseidon — iterative fold over Field[]
// ---------------------------------------------------------------------------

const PoseidonProgram = ZkProgram({
    name: "PoseidonBench",
    publicInput: Field, // dummy
    methods: {
        hash: {
            privateInputs: [Provable.Array(Field, INPUT_SIZE)],
            async method(_pub: Field, inputs: Field[]): Promise<void> {
                // state = Poseidon(elem[0])
                let state = Poseidon.hash([inputs[0]]);
                // state = Poseidon(state, elem[i])  for i = 1..N-1
                for (let i = 1; i < INPUT_SIZE; i++) {
                    state = Poseidon.hash([state, inputs[i]]);
                }
                state.assertNotEquals(Field(-1));
            },
        },
    },
});

// ---------------------------------------------------------------------------
// 2. SHA2-256 — iterative, converting each Field to 31 bytes in-circuit
// ---------------------------------------------------------------------------

const Sha256Program = ZkProgram({
    name: "Sha256Bench",
    publicInput: Field,
    methods: {
        hash: {
            privateInputs: [Provable.Array(Field, INPUT_SIZE)],
            async method(_pub: Field, inputs: Field[]): Promise<void> {
                // First step: hash(elem[0])  →  Bytes31 input
                const first = Bytes31.from(fieldToBytes31(inputs[0]));
                let digest = Hash.SHA2_256.hash(first);

                // Next steps: hash(digest[0..30] || elem[i])  →  Bytes62 input
                for (let i = 1; i < INPUT_SIZE; i++) {
                    const combined = Bytes62.from([
                        ...digestTo31(digest),
                        ...fieldToBytes31(inputs[i]),
                    ]);
                    digest = Hash.SHA2_256.hash(combined);
                }
                digest.bytes[0].value.assertNotEquals(Field(-1));
            },
        },
    },
});

// ---------------------------------------------------------------------------
// 3. Keccak256 — same structure as SHA256
// ---------------------------------------------------------------------------

const Keccak256Program = ZkProgram({
    name: "Keccak256Bench",
    publicInput: Field,
    methods: {
        hash: {
            privateInputs: [Provable.Array(Field, INPUT_SIZE)],
            async method(_pub: Field, inputs: Field[]): Promise<void> {
                const first = Bytes31.from(fieldToBytes31(inputs[0]));
                let digest = Hash.Keccak256.hash(first);

                for (let i = 1; i < INPUT_SIZE; i++) {
                    const combined = Bytes62.from([
                        ...digestTo31(digest),
                        ...fieldToBytes31(inputs[i]),
                    ]);
                    digest = Hash.Keccak256.hash(combined);
                }
                digest.bytes[0].value.assertNotEquals(Field(-1));
            },
        },
    },
});

// ---------------------------------------------------------------------------
// 4. Blake2b — same structure
// ---------------------------------------------------------------------------

const Blake2bProgram = ZkProgram({
    name: "Blake2bBench",
    publicInput: Field,
    methods: {
        hash: {
            privateInputs: [Provable.Array(Field, INPUT_SIZE)],
            async method(_pub: Field, inputs: Field[]): Promise<void> {
                const first = Bytes31.from(fieldToBytes31(inputs[0]));
                let digest = Hash.BLAKE2B.hash(first);

                for (let i = 1; i < INPUT_SIZE; i++) {
                    const combined = Bytes62.from([
                        ...digestTo31(digest),
                        ...fieldToBytes31(inputs[i]),
                    ]);
                    digest = Hash.BLAKE2B.hash(combined);
                }
                digest.bytes[0].value.assertNotEquals(Field(-1));
            },
        },
    },
});

// ---------------------------------------------------------------------------
// Benchmark helpers
// ---------------------------------------------------------------------------

interface BenchResult {
    name: string;
    constraints: number;
    compileMs: number;
    proveMs: number;
    verifyMs: number;
    totalMs: number;
}

function separator(title: string) {
    console.log("\n" + "─".repeat(62));
    console.log(`  ${title}`);
    console.log("─".repeat(62));
}

async function runBench<P extends {
    analyzeMethods(): Promise<Record<string, { rows: number }>>;
    compile(): Promise<unknown>;
    verify(proof: unknown): Promise<boolean>;
}>(
    program: P,
    methodName: string,
    prove: () => Promise<{ proof: unknown }>,
    name: string
): Promise<BenchResult> {
    separator(`Benchmarking: ${name}`);

    const analysis = await program.analyzeMethods();
    const constraints = (analysis[methodName] as { rows: number }).rows;
    console.log(`  Constraints : ${constraints.toLocaleString()}`);

    const t0 = performance.now();
    await program.compile();
    const compileMs = Math.round(performance.now() - t0);
    console.log(`  Compile     : ${compileMs} ms`);

    const t1 = performance.now();
    const { proof } = await prove();
    const proveMs = Math.round(performance.now() - t1);
    console.log(`  Prove       : ${proveMs} ms`);

    const t2 = performance.now();
    const ok = await program.verify(proof);
    const verifyMs = Math.round(performance.now() - t2);
    console.log(`  Verify      : ${verifyMs} ms  (valid=${ok})`);

    const totalMs = compileMs + proveMs + verifyMs;
    console.log(`  TOTAL       : ${totalMs} ms`);

    return { name, constraints, compileMs, proveMs, verifyMs, totalMs };
}

// ---------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------

async function main() {
    console.log("\n╔════════════════════════════════════════════════════════════╗");
    console.log(`║  o1js Hash Benchmark — ${INPUT_SIZE} inputs, iterative fold          ║`);
    console.log("║  Poseidon  /  SHA2-256  /  Keccak256  /  Blake2b          ║");
    console.log("╚════════════════════════════════════════════════════════════╝");

    // 5 deterministic field elements: Field(1) .. Field(5)
    const inputs: Field[] = Array.from({ length: INPUT_SIZE }, (_, i) =>
        Field(i + 1)
    );
    const pub = Field(0); // dummy public input

    const results: BenchResult[] = [];

    results.push(
        await runBench(
            PoseidonProgram, "hash",
            () => PoseidonProgram.hash(pub, inputs),
            "Poseidon (native)"
        )
    );

    results.push(
        await runBench(
            Sha256Program, "hash",
            () => Sha256Program.hash(pub, inputs),
            "SHA2-256"
        )
    );

    results.push(
        await runBench(
            Keccak256Program, "hash",
            () => Keccak256Program.hash(pub, inputs),
            "Keccak256"
        )
    );

    results.push(
        await runBench(
            Blake2bProgram, "hash",
            () => Blake2bProgram.hash(pub, inputs),
            "Blake2b"
        )
    );

    // ── Summary ───────────────────────────────────────────────────────────────
    separator("Summary");

    const p = (s: string, n: number) => s.padEnd(n);
    const r = (s: string, n: number) => s.padStart(n);

    console.log(
        p("Hash", 20) +
        r("Rows", 10) +
        r("Compile(ms)", 14) +
        r("Prove(ms)", 16) +
        r("Verify(ms)", 13) +
        r("Total(ms)", 12)
    );
    console.log("─".repeat(85));

    const baseline = results[0].proveMs || 1;
    for (const res of results) {
        const mult = (res.proveMs / baseline).toFixed(1);
        console.log(
            p(res.name, 20) +
            r(res.constraints.toLocaleString(), 10) +
            r(res.compileMs.toString(), 14) +
            r(`${res.proveMs} (${mult}×)`, 16) +
            r(res.verifyMs.toString(), 13) +
            r(res.totalMs.toString(), 12)
        );
    }

    console.log(`\n  ${INPUT_SIZE} inputs per program, iterative: state = hash(state || elem[i])`);
    console.log("  Rows = circuit rows reported by analyzeMethods()");
    console.log("  Prove ratio relative to Poseidon baseline (1×)\n");
}

main().catch((e) => {
    console.error(e);
    process.exit(1);
});