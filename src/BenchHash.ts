/**
 * BenchHash.ts
 *
 * Benchmark 4 ZK programs with different hash functions in o1js:
 *   1. Poseidon    — native Mina/Pasta field hash
 *   2. SHA2-256    — Hash.SHA2_256
 *   3. Keccak256   — Hash.Keccak256
 *   4. Blake2b     — Hash.BLAKE2B
 *
 * Each program hashes 4 field elements / bytes and logs:
 *   - constraint count
 *   - compile time
 *   - prove time
 *   - verify time
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
} from "o1js";

// ---------------------------------------------------------------------------
// Shared inputs
// ---------------------------------------------------------------------------

// 4 field elements used by Poseidon
const FIELDS: Field[] = [Field(1), Field(2), Field(3), Field(4)];

// 32 bytes used by SHA256 / Keccak256 / Blake2b
// Encode the 4 values as 8-byte chunks packed into 32 bytes
class Bytes32 extends Bytes(32) { }

function makeBytes32(): Bytes32 {
    const raw: UInt8[] = Array.from({ length: 32 }, (_, i) =>
        UInt8.from(i + 1)
    );
    return Bytes32.from(raw);
}

// ---------------------------------------------------------------------------
// Logging helpers
// ---------------------------------------------------------------------------

function separator(title: string) {
    console.log("\n" + "─".repeat(62));
    console.log(`  ${title}`);
    console.log("─".repeat(62));
}

// ---------------------------------------------------------------------------
// 1. Poseidon — native Mina hash over Field[]
// ---------------------------------------------------------------------------

const PoseidonProgram = ZkProgram({
    name: "PoseidonBench",
    publicInput: Field, // dummy public input to satisfy the API
    methods: {
        hash: {
            privateInputs: [Field, Field, Field, Field],
            async method(
                _pub: Field,
                a: Field,
                b: Field,
                c: Field,
                d: Field
            ): Promise<void> {
                const result = Poseidon.hash([a, b, c, d]);
                // Constrain result so the compiler can't eliminate the computation
                result.assertNotEquals(Field(-1));
            },
        },
    },
});

// ---------------------------------------------------------------------------
// 2. SHA2-256 — Hash.SHA2_256 over Bytes32
// ---------------------------------------------------------------------------

const Sha256Program = ZkProgram({
    name: "Sha256Bench",
    publicInput: Field,
    methods: {
        hash: {
            privateInputs: [Bytes32],
            async method(_pub: Field, input: Bytes32): Promise<void> {
                const digest = Hash.SHA2_256.hash(input);
                // Constrain first byte so computation is not eliminated
                digest.bytes[0].value.assertNotEquals(Field(-1));
            },
        },
    },
});

// ---------------------------------------------------------------------------
// 3. Keccak256 — Hash.Keccak256 over Bytes32
// ---------------------------------------------------------------------------

const Keccak256Program = ZkProgram({
    name: "Keccak256Bench",
    publicInput: Field,
    methods: {
        hash: {
            privateInputs: [Bytes32],
            async method(_pub: Field, input: Bytes32): Promise<void> {
                const digest = Hash.Keccak256.hash(input);
                digest.bytes[0].value.assertNotEquals(Field(-1));
            },
        },
    },
});

// ---------------------------------------------------------------------------
// 4. Blake2b — Hash.BLAKE2B over Bytes32
// ---------------------------------------------------------------------------

const Blake2bProgram = ZkProgram({
    name: "Blake2bBench",
    publicInput: Field,
    methods: {
        hash: {
            privateInputs: [Bytes32],
            async method(_pub: Field, input: Bytes32): Promise<void> {
                const digest = Hash.BLAKE2B.hash(input);
                digest.bytes[0].value.assertNotEquals(Field(-1));
            },
        },
    },
});

// ---------------------------------------------------------------------------
// Benchmark runner
// ---------------------------------------------------------------------------

interface BenchResult {
    name: string;
    constraints: number;
    compileMs: number;
    proveMs: number;
    verifyMs: number;
    totalMs: number;
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

    // Constraint count
    const analysis = await program.analyzeMethods();
    const constraints = (analysis[methodName] as { rows: number }).rows;
    console.log(`  Constraints : ${constraints.toLocaleString()}`);

    // Compile
    const t0 = performance.now();
    await program.compile();
    const compileMs = Math.round(performance.now() - t0);
    console.log(`  Compile     : ${compileMs} ms`);

    // Prove
    const t1 = performance.now();
    const { proof } = await prove();
    const proveMs = Math.round(performance.now() - t1);
    console.log(`  Prove       : ${proveMs} ms`);

    // Verify
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
    console.log("║  o1js Hash Benchmark — 4 inputs per program               ║");
    console.log("║  Poseidon  /  SHA2-256  /  Keccak256  /  Blake2b          ║");
    console.log("╚════════════════════════════════════════════════════════════╝");

    const bytes = makeBytes32();
    const pub = Field(0); // dummy public input

    const results: BenchResult[] = [];

    // 1. Poseidon
    results.push(
        await runBench(
            PoseidonProgram,
            "hash",
            () => PoseidonProgram.hash(pub, FIELDS[0], FIELDS[1], FIELDS[2], FIELDS[3]),
            "Poseidon (native)"
        )
    );

    // 2. SHA2-256
    results.push(
        await runBench(
            Sha256Program,
            "hash",
            () => Sha256Program.hash(pub, bytes),
            "SHA2-256"
        )
    );

    // 3. Keccak256
    results.push(
        await runBench(
            Keccak256Program,
            "hash",
            () => Keccak256Program.hash(pub, bytes),
            "Keccak256"
        )
    );

    // 4. Blake2b
    results.push(
        await runBench(
            Blake2bProgram,
            "hash",
            () => Blake2bProgram.hash(pub, bytes),
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
        r("Prove(ms)", 14) +
        r("Verify(ms)", 13) +
        r("Total(ms)", 12)
    );
    console.log("─".repeat(83));

    const baseline = results[0].proveMs || 1;

    for (const res of results) {
        const mult = (res.proveMs / baseline).toFixed(1);
        console.log(
            p(res.name, 20) +
            r(res.constraints.toLocaleString(), 10) +
            r(res.compileMs.toString(), 14) +
            r(`${res.proveMs} (${mult}×)`, 14) +
            r(res.verifyMs.toString(), 13) +
            r(res.totalMs.toString(), 12)
        );
    }

    console.log("\n  Prove time ratio relative to Poseidon (baseline = 1×)");
    console.log("  Rows = circuit rows (constraints) reported by analyzeMethods\n");
}

main().catch((e) => {
    console.error(e);
    process.exit(1);
});