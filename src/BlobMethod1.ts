/**
 * KZG Blob Evaluation — Method 1 Merkle-binding circuit (o1js / Kimchi)
 *
 * Based on Dankrad's Method 1 from:
 * https://notes.ethereum.org/@dankrad/kzg_commitments_in_proofs
 *
 * What this circuit proves:
 *   "There exist 4096 private blob values, committed by merkleRoot, such that
 *    f(z) = y where z = Poseidon(C0, C1, merkleRoot)"
 *
 * What SP1 must prove externally to complete Method 1:
 *   1. merkleRoot == PoseidonMerkle(blob)   — same leaf encoding as circuit
 *   2. C_kzg == KZGCommit(blob)             — using trusted setup
 *   3. KZG.verify(C_kzg, z, y, π_kzg)      — opening proof at the circuit's z
 *
 * Design decisions:
 *
 *   C  — represented as (C0: Field, C1: Field), the high/low 128-bit halves
 *        of the EIP-4844 versioned hash.  No bits are dropped.
 *
 *   z  — derived in finalize as Poseidon(C0, C1, merkleRoot).  Both C and
 *        merkleRoot are public outputs, so any verifier can recompute z.
 *        The same z is used for the external KZG point-opening check.
 *
 *   z ∉ domain — asserted off-circuit before proving.  For a Poseidon-derived
 *        challenge the probability of z landing on one of the 4096 domain
 *        points is 4096 / BLS_MODULUS ≈ 2^{-242}, negligible at 128-bit
 *        security.  No in-circuit conditional branch is added because it
 *        would cost ~300 rows and the assumption is cryptographically sound.
 */

import {
    Field,
    Poseidon,
    Provable,
    Struct,
    ZkProgram,
    SelfProof,
    createForeignField,
    verify,
    Cache,
    setBackend,
} from 'o1js';

import cKzg from 'c-kzg';
import type { Blob, Bytes32, Bytes48 } from 'c-kzg';

import { createHash } from 'node:crypto';
import { readFileSync, existsSync } from 'node:fs';
import path from 'node:path';

setBackend('native');

const {
    BYTES_PER_BLOB,
    BYTES_PER_COMMITMENT,
    BYTES_PER_FIELD_ELEMENT,
    BYTES_PER_PROOF,
    FIELD_ELEMENTS_PER_BLOB,
    blobToKzgCommitment,
    computeKzgProof,
    computeBlobKzgProof,
    verifyKzgProof,
    verifyBlobKzgProof,
    verifyBlobKzgProofBatch,
    loadTrustedSetup,
} = cKzg;

// ---------------------------------------------------------------------------
// Constants
// ---------------------------------------------------------------------------

const BLS_MODULUS =
    52435875175126190479447740508185965837690552500527637822603658699938581184513n;

const LOG2_BLOB_SIZE = 12;
const PRIMITIVE_ROOT_OF_UNITY = 7n;
const BYTES_PER_FIELD = 32;
const CHUNK_SIZE = 256;
const NUM_CHUNKS = FIELD_ELEMENTS_PER_BLOB / CHUNK_SIZE; // 16
const LOG2_CHUNK_SIZE = 8; // log2(256) levels of Poseidon per leaf

const KZG_VERSION_BYTE = 0x01;

const PROJECT_ROOT = process.cwd();
const BLOB_JSON_PATH = path.join(PROJECT_ROOT, 'blob.json');
const TRUSTED_SETUP_PATH = path.join(PROJECT_ROOT, 'trusted_setup.txt');

const cache = Cache.FileSystem('./cache');

// ---------------------------------------------------------------------------
// Foreign field — BLS12-381 scalar field
// ---------------------------------------------------------------------------

class BlsFr extends createForeignField(BLS_MODULUS) { }
class BlsFrAlmost extends BlsFr.AlmostReduced { }
class BlsFrCanonical extends BlsFr.Canonical { }

type BlsFrA = InstanceType<typeof BlsFrAlmost>;
type BlsFrC = InstanceType<typeof BlsFrCanonical>;
type BlsFrU = InstanceType<typeof BlsFr>;

const ChunkArray = Provable.Array(BlsFrAlmost, CHUNK_SIZE);
// ChunkRootsArray removed — roots are compile-time constants per leaf_k, never witness variables

const WIDTH = new BlsFrCanonical(BigInt(FIELD_ELEMENTS_PER_BLOB));
const ONE = new BlsFrCanonical(1n);
const CHUNK_SIGNS = Array.from({ length: CHUNK_SIZE - 1 }, () => 1 as const) as (1 | -1)[];

// ---------------------------------------------------------------------------
// JSON input type
// ---------------------------------------------------------------------------

type BlobJson = { blobHex: string; commitmentHex: string; proofHex: string };

// ---------------------------------------------------------------------------
// Basic helpers
// ---------------------------------------------------------------------------

function mod(x: bigint): bigint {
    const r = x % BLS_MODULUS;
    return r >= 0n ? r : r + BLS_MODULUS;
}

function modPow(base: bigint, exp: bigint, modulus: bigint): bigint {
    let result = 1n, b = mod(base), e = exp;
    while (e > 0n) {
        if (e & 1n) result = (result * b) % modulus;
        b = (b * b) % modulus;
        e >>= 1n;
    }
    return result;
}

function modInv(x: bigint): bigint {
    if (x === 0n) throw new Error('Division by zero');
    return modPow(mod(x), BLS_MODULUS - 2n, BLS_MODULUS);
}

function strip0x(hex: string): string { return hex.startsWith('0x') ? hex.slice(2) : hex; }

function hexToBytes(hex: string): Uint8Array {
    const clean = strip0x(hex);
    if (clean.length % 2 !== 0) throw new Error('Odd hex string');
    return Uint8Array.from(Buffer.from(clean, 'hex'));
}

function bytesToHex(b: Uint8Array): string { return `0x${Buffer.from(b).toString('hex')}`; }
function bytesToBigintBE(b: Uint8Array): bigint { return BigInt(`0x${Buffer.from(b).toString('hex')}`); }

function bigintToBytesBE(x: bigint, len: number): Uint8Array {
    return Uint8Array.from(Buffer.from(x.toString(16).padStart(len * 2, '0'), 'hex'));
}

function equalBytes(a: Uint8Array, b: Uint8Array): boolean { return Buffer.from(a).equals(Buffer.from(b)); }
function sha256(data: Uint8Array): Uint8Array { return Uint8Array.from(createHash('sha256').update(data).digest()); }

// ---------------------------------------------------------------------------
// FIX 3 — C represented as two Fields, no bits dropped
//
// versioned hash = 0x01 || sha256(commitment)[1:]  — 32 bytes
// Split into:
//   C0 = high 128 bits (bytes  0..15)  — contains the 0x01 version byte
//   C1 = low  128 bits (bytes 16..31)
//
// Both fit in a Mina Field (< 2^128 < Mina prime).
// Reconstructing the full hash: (C0 << 128) | C1 — no information lost.
// ---------------------------------------------------------------------------

function kzgCommitmentToVersionedHash(commitmentBytes: Uint8Array): Uint8Array {
    const hash = sha256(commitmentBytes);
    hash[0] = KZG_VERSION_BYTE;
    return hash; // 32 bytes
}

function versionedHashToFields(versionedHash: Uint8Array): { C0: bigint; C1: bigint } {
    const full = bytesToBigintBE(versionedHash); // 256-bit integer
    const C0 = full >> 128n;                      // high 128 bits
    const C1 = full & ((1n << 128n) - 1n);        // low 128 bits
    return { C0, C1 };
}

// ---------------------------------------------------------------------------
// Blob parsing
// ---------------------------------------------------------------------------

function blobBytesToFieldElements(blobBytes: Uint8Array): bigint[] {
    if (blobBytes.length !== BYTES_PER_BLOB)
        throw new Error(`Invalid blob length: ${blobBytes.length}`);
    return Array.from({ length: FIELD_ELEMENTS_PER_BLOB }, (_, i) => {
        const x = bytesToBigintBE(blobBytes.slice(i * BYTES_PER_FIELD_ELEMENT, (i + 1) * BYTES_PER_FIELD_ELEMENT));
        if (x >= BLS_MODULUS) throw new Error(`Element ${i} >= BLS_MODULUS`);
        return x;
    });
}

// ---------------------------------------------------------------------------
// Roots of unity (Deneb bit-reversal permutation)
// ---------------------------------------------------------------------------

function reverseBits(n: number, order: number): number {
    const w = order.toString(2).length - 1;
    return Number.parseInt(n.toString(2).padStart(w, '0').split('').reverse().join(''), 2);
}

function bitReversalPermutation<T>(seq: T[]): T[] {
    return seq.map((_, i) => seq[reverseBits(i, seq.length)]);
}

function computePowers(x: bigint, n: number): bigint[] {
    const out: bigint[] = [];
    let cur = 1n;
    for (let i = 0; i < n; i++) { out.push(cur); cur = mod(cur * x); }
    return out;
}

function computeRootsOfUnity(order: number): bigint[] {
    return computePowers(modPow(PRIMITIVE_ROOT_OF_UNITY, (BLS_MODULUS - 1n) / BigInt(order), BLS_MODULUS), order);
}

const ROOTS_BIGINT = bitReversalPermutation(computeRootsOfUnity(FIELD_ELEMENTS_PER_BLOB));
const ROOTS = ROOTS_BIGINT.map(x => new BlsFrCanonical(x));
const ROOTS_SET = new Set(ROOTS_BIGINT.map(x => x.toString()));

const CHUNK_ROOTS: BlsFrC[][] = Array.from({ length: NUM_CHUNKS }, (_, k) =>
    ROOTS.slice(k * CHUNK_SIZE, (k + 1) * CHUNK_SIZE)
);

// ---------------------------------------------------------------------------
// Off-circuit evaluator
//
// FIX 2 (partial) — z ∉ domain is asserted by the caller before this runs.
// The circuit never branches on z == w_i; instead we guarantee off-circuit
// that this case cannot arise for a Poseidon-derived challenge.
// Probability: 4096 / BLS_MODULUS ≈ 2^{-242} — negligible at 128-bit security.
// ---------------------------------------------------------------------------

function evaluateBlobOffCircuit(blob: bigint[], z: bigint): bigint {
    // Caller must assert z ∉ ROOTS_SET before calling this.
    let sum = 0n;
    for (let i = 0; i < FIELD_ELEMENTS_PER_BLOB; i++) {
        const den = mod(z - ROOTS_BIGINT[i]);
        sum = mod(sum + mod(mod(blob[i] * ROOTS_BIGINT[i]) * modInv(den)));
    }
    const scale = mod(mod(modPow(z, BigInt(FIELD_ELEMENTS_PER_BLOB), BLS_MODULUS) - 1n) * modInv(BigInt(FIELD_ELEMENTS_PER_BLOB)));
    return mod(scale * sum);
}

// ---------------------------------------------------------------------------
// Off-circuit Merkle root + z derivation
//
// Mirrors exactly what the circuit computes so that finalize's assertion
//   z == Poseidon(C0, C1, merkleRoot)
// is satisfied.
//
// Poseidon.hash() on Field constants is safe outside ZkProgram methods.
// ---------------------------------------------------------------------------

function blobElemToLeafField(x: bigint): Field {
    const mask88 = (1n << 88n) - 1n;
    return Poseidon.hash([Field(x & mask88), Field((x >> 88n) & mask88), Field(x >> 176n)]);
}

function computeMerkleRootOffCircuit(
    blobBigints: bigint[],
    C0: bigint,
    C1: bigint,
): { merkleRoot: Field; z: BlsFrC; zBigint: bigint } {
    // Build full Poseidon Merkle tree
    let leaves: Field[] = blobBigints.map(blobElemToLeafField);
    while (leaves.length > 1) {
        const next: Field[] = [];
        for (let i = 0; i < leaves.length; i += 2)
            next.push(Poseidon.hash([leaves[i], leaves[i + 1]]));
        leaves = next;
    }
    const merkleRoot = leaves[0];

    // z = Poseidon(C0, C1, merkleRoot) — mirrors finalize in-circuit
    const zField = Poseidon.hash([Field(C0), Field(C1), merkleRoot]);
    const zBigint = zField.toBigInt() % BLS_MODULUS;

    return { merkleRoot, z: new BlsFrCanonical(zBigint), zBigint };
}

// ---------------------------------------------------------------------------
// Input loading
// ---------------------------------------------------------------------------

function loadBlobJson(): BlobJson {
    if (!existsSync(BLOB_JSON_PATH)) throw new Error(`Missing blob.json at: ${BLOB_JSON_PATH}`);
    const p = JSON.parse(readFileSync(BLOB_JSON_PATH, 'utf8')) as Partial<BlobJson>;
    if (!p.blobHex || !p.commitmentHex || !p.proofHex)
        throw new Error('blob.json must contain blobHex, commitmentHex, proofHex');
    return { blobHex: p.blobHex, commitmentHex: p.commitmentHex, proofHex: p.proofHex };
}

function loadBlobscanCase() {
    const { blobHex, commitmentHex, proofHex } = loadBlobJson();
    const blobBytes = hexToBytes(blobHex);
    const commitmentBytes = hexToBytes(commitmentHex);
    const proofBytes = hexToBytes(proofHex);
    const blob = blobBytes as Blob;
    const commitment = commitmentBytes as Bytes48;
    const proof = proofBytes as Bytes48;

    const blobBigints = blobBytesToFieldElements(blobBytes);

    // FIX 3 — C as two lossless Fields
    const versionedHash = kzgCommitmentToVersionedHash(commitmentBytes);
    const { C0, C1 } = versionedHashToFields(versionedHash);

    // Blob-level KZG checks (no z needed)
    const computedCommitmentBytes = Uint8Array.from(blobToKzgCommitment(blob));
    const commitmentMatches = equalBytes(computedCommitmentBytes, commitmentBytes);
    const proofVerifies = verifyBlobKzgProof(blob, commitment, proof);
    const proofBatchVerifies = verifyBlobKzgProofBatch([blob], [commitment], [proof]);
    const computedBlobProofBytes = Uint8Array.from(computeBlobKzgProof(blob, commitment));
    const blobProofMatches = equalBytes(computedBlobProofBytes, proofBytes);

    // FIX 1 — point-opening KZG check is NOT done here.
    // It requires z = Poseidon(C0, C1, merkleRoot) which is only known after
    // computeMerkleRootOffCircuit() runs in main().

    return {
        blobBytes, commitmentBytes, proofBytes, blobBigints,
        versionedHash, C0, C1,
        blob, commitment,
        computedCommitmentBytes, commitmentMatches,
        proofVerifies, proofBatchVerifies,
        computedBlobProofBytes, blobProofMatches,
    };
}

// ---------------------------------------------------------------------------
// Public output
// ---------------------------------------------------------------------------

class BlobEvalOutput extends Struct({
    C0: Field,           // high 128 bits of EIP-4844 versioned hash
    C1: Field,           // low  128 bits of EIP-4844 versioned hash
    merkleRoot: Field,           // Poseidon Merkle root of all 4096 blob elements
    z: BlsFrCanonical,  // Poseidon(C0, C1, merkleRoot) — derived in finalize
    partialSum: BlsFrAlmost,     // y = f(z) after finalize
    chunksDone: Field,
}) { }

// ---------------------------------------------------------------------------
// Circuit helpers
// ---------------------------------------------------------------------------

function squareRepeatedly(x: BlsFrA | BlsFrC, rounds: number): BlsFrA {
    let acc = x as unknown as BlsFrA;
    for (let i = 0; i < rounds; i++) acc = acc.mul(acc).assertAlmostReduced() as BlsFrA;
    return acc;
}

function batchInvert(xs: BlsFrA[]): BlsFrA[] {
    const n = xs.length;
    if (n === 0) return [];
    if (n === 1) return [xs[0].inv().assertAlmostReduced() as BlsFrA];
    const prefix = new Array<BlsFrA>(n);
    prefix[0] = xs[0];
    for (let i = 1; i < n; i++) prefix[i] = prefix[i - 1].mul(xs[i]).assertAlmostReduced() as BlsFrA;
    const invProd = prefix[n - 1].inv().assertAlmostReduced() as BlsFrA;
    const inv = new Array<BlsFrA>(n);
    let suffix = invProd;
    for (let i = n - 1; i >= 1; i--) {
        inv[i] = suffix.mul(prefix[i - 1]).assertAlmostReduced() as BlsFrA;
        suffix = suffix.mul(xs[i]).assertAlmostReduced() as BlsFrA;
    }
    inv[0] = suffix;
    return inv;
}

// FIX 2 — z ∉ domain is guaranteed by the caller (asserted in main before proving).
// No in-circuit conditional branch: adding Provable.if for each of the 256
// denominators would cost ~300 extra rows per chunk for a 2^{-242} probability
// event. The assumption is documented and enforced off-circuit.
function evalChunk(chunk: BlsFrA[], chunkRoots: BlsFrC[], z: BlsFrC): BlsFrA {
    const nums = chunk.map((fi, i) => fi.mul(chunkRoots[i]).assertAlmostReduced() as BlsFrA);
    const dens = chunkRoots.map(w => z.sub(w).assertAlmostReduced() as BlsFrA);
    const invs = batchInvert(dens);
    const terms = nums.map((n, i) => n.mul(invs[i])) as BlsFrU[];
    return BlsFr.sum(terms, CHUNK_SIGNS).assertAlmostReduced() as BlsFrA;
}

function chunkToSubMerkleRoot(chunk: BlsFrA[]): Field {
    // Leaf: hash the 3 × 88-bit limbs of each BLS element
    let leaves: Field[] = chunk.map(fi => {
        const [l0, l1, l2] = fi.value;
        return Poseidon.hash([l0, l1, l2]);
    });
    // LOG2_CHUNK_SIZE = 8 levels → 255 hashes per chunk
    for (let level = 0; level < LOG2_CHUNK_SIZE; level++) {
        const next: Field[] = [];
        for (let i = 0; i < leaves.length; i += 2)
            next.push(Poseidon.hash([leaves[i], leaves[i + 1]]));
        leaves = next;
    }
    return leaves[0];
}

// ---------------------------------------------------------------------------
// ZkProgram
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// Method builder
//
// leaf_k — each captures CHUNK_ROOTS[k] as a compile-time constant closure.
// This means the 256 roots are constants in the circuit (0 witness cells,
// 0 rows) rather than 768 witness variables that bloat the SRS encoding.
// ---------------------------------------------------------------------------

function buildMethods() {
    const leaves: Record<string, {
        privateInputs: [typeof BlsFrCanonical, typeof Field, typeof Field, typeof ChunkArray];
        method: (z: BlsFrC, C0: Field, C1: Field, chunk: BlsFrA[]) => Promise<{ publicOutput: BlobEvalOutput }>;
    }> = {};

    for (let k = 0; k < NUM_CHUNKS; k++) {
        const kRoots = CHUNK_ROOTS[k]; // compile-time constant slice for leaf k
        leaves[`leaf_${k}`] = {
            privateInputs: [BlsFrCanonical, Field, Field, ChunkArray],
            async method(z: BlsFrC, C0: Field, C1: Field, chunk: BlsFrA[]): Promise<{ publicOutput: BlobEvalOutput }> {
                const partialSum = evalChunk(chunk, kRoots, z);
                const merkleRoot = chunkToSubMerkleRoot(chunk);
                return {
                    publicOutput: new BlobEvalOutput({
                        C0, C1, merkleRoot, z,
                        partialSum,
                        chunksDone: Field(CHUNK_SIZE),
                    }),
                };
            },
        };
    }

    return leaves;
}

const BlobEvalProgram = ZkProgram({
    name: 'blob-eval-4096-method1-merkle-binding',
    publicOutput: BlobEvalOutput,

    methods: {
        ...buildMethods(),

        // ── merge ─────────────────────────────────────────────────────────
        merge: {
            privateInputs: [SelfProof, SelfProof] as const,

            async method(
                leftProof: SelfProof<undefined, BlobEvalOutput>,
                rightProof: SelfProof<undefined, BlobEvalOutput>,
            ): Promise<{ publicOutput: BlobEvalOutput }> {
                leftProof.verify();
                rightProof.verify();

                const l = leftProof.publicOutput;
                const r = rightProof.publicOutput;

                l.z.assertEquals(r.z, 'merge: z mismatch');
                l.C0.assertEquals(r.C0, 'merge: C0 mismatch');
                l.C1.assertEquals(r.C1, 'merge: C1 mismatch');

                const combinedSum = l.partialSum.add(r.partialSum).assertAlmostReduced() as BlsFrA;
                const combinedChunks = l.chunksDone.add(r.chunksDone);
                const combinedRoot = Poseidon.hash([l.merkleRoot, r.merkleRoot]);

                return {
                    publicOutput: new BlobEvalOutput({
                        C0: l.C0,
                        C1: l.C1,
                        merkleRoot: combinedRoot,
                        z: l.z,
                        partialSum: combinedSum,
                        chunksDone: combinedChunks,
                    }),
                };
            },
        },

        // ── finalize ──────────────────────────────────────────────────────
        // FIX 1 + 3 — z is re-derived from (C0, C1, merkleRoot), all public.
        // Uses all 256 bits of the versioned hash (no truncation).
        finalize: {
            privateInputs: [SelfProof] as const,

            async method(
                rootProof: SelfProof<undefined, BlobEvalOutput>,
            ): Promise<{ publicOutput: BlobEvalOutput }> {
                rootProof.verify();

                const root = rootProof.publicOutput;
                root.chunksDone.assertEquals(
                    Field(FIELD_ELEMENTS_PER_BLOB),
                    'finalize: tree does not cover the full blob',
                );

                // Derive z from public data — mirrors computeMerkleRootOffCircuit
                const zField = Poseidon.hash([root.C0, root.C1, root.merkleRoot]);

                // Assert z carried through the proof == derived value.
                // Limb reconstruction: integer = l0 + l1·2^88 + l2·2^176
                const [l0, l1, l2] = root.z.value;
                const TWO_88 = Field(2n ** 88n);
                const TWO_176 = Field(2n ** 176n);
                l0.add(l1.mul(TWO_88)).add(l2.mul(TWO_176))
                    .assertEquals(zField, 'finalize: z != Poseidon(C0, C1, merkleRoot)');

                const zPowN = squareRepeatedly(root.z, LOG2_BLOB_SIZE);
                const scale = zPowN.sub(ONE).assertAlmostReduced().div(WIDTH);
                const y = scale.mul(root.partialSum).assertAlmostReduced() as BlsFrA;

                return {
                    publicOutput: new BlobEvalOutput({
                        C0: root.C0,
                        C1: root.C1,
                        merkleRoot: root.merkleRoot,
                        z: root.z,
                        partialSum: y,
                        chunksDone: Field(FIELD_ELEMENTS_PER_BLOB + 1),
                    }),
                };
            },
        },
    },
});

class BlobEvalProof extends ZkProgram.Proof(BlobEvalProgram) { }

// ---------------------------------------------------------------------------
// Sequential tree prover
// ---------------------------------------------------------------------------

// Dynamic dispatch to leaf_k methods
type Prog = typeof BlobEvalProgram & Record<string, (...args: any[]) => Promise<{ proof: BlobEvalProof }>>;
const prog = BlobEvalProgram as Prog;

async function proveTree(
    blobChunks: BlsFrA[][],
    z: BlsFrC,
    C0: Field,
    C1: Field,
): Promise<BlobEvalProof> {
    console.log(`  [level 0] proving ${NUM_CHUNKS} leaves sequentially...`);
    console.time('  level-0');
    const leaves: BlobEvalProof[] = [];
    for (let k = 0; k < NUM_CHUNKS; k++) {
        const { proof } = await prog[`leaf_${k}`](z, C0, C1, blobChunks[k]);
        leaves.push(proof as BlobEvalProof);
        console.log(`    leaf ${k + 1}/${NUM_CHUNKS} done`);
    }
    console.timeEnd('  level-0');

    let level: BlobEvalProof[] = leaves;
    let depth = 1;
    while (level.length > 1) {
        console.log(`  [level ${depth}] merging ${level.length / 2} pairs...`);
        console.time(`  level-${depth}`);
        const next: BlobEvalProof[] = [];
        for (let i = 0; i < level.length; i += 2) {
            const { proof } = await BlobEvalProgram.merge(level[i], level[i + 1]);
            next.push(proof as BlobEvalProof);
        }
        level = next;
        console.timeEnd(`  level-${depth}`);
        depth++;
    }

    console.log('  [finalize]...');
    console.time('  finalize');
    const { proof } = await BlobEvalProgram.finalize(level[0]);
    console.timeEnd('  finalize');
    return proof as BlobEvalProof;
}

// ---------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------

async function main() {
    console.log('=== KZG Blob Eval — Method 1 Merkle-binding circuit ===\n');

    if (ROOTS_SET.size !== FIELD_ELEMENTS_PER_BLOB) throw new Error('Invalid roots precomputation');
    if (!existsSync(TRUSTED_SETUP_PATH)) throw new Error(`Missing: ${TRUSTED_SETUP_PATH}`);
    loadTrustedSetup(0, TRUSTED_SETUP_PATH);

    console.time('load-input');
    const input = loadBlobscanCase();
    console.timeEnd('load-input');

    console.log('\n=== Blob-level c-kzg checks (no z needed) ===');
    console.log('commitment matches  :', input.commitmentMatches);
    console.log('blob proof verifies :', input.proofVerifies);
    console.log('batch verifies      :', input.proofBatchVerifies);
    console.log('blob proof matches  :', input.blobProofMatches);
    console.log('versioned hash      :', bytesToHex(input.versionedHash));
    console.log('C0 (high 128 bits)  :', input.C0.toString(16));
    console.log('C1 (low  128 bits)  :', input.C1.toString(16));

    // Compute merkleRoot and z = Poseidon(C0, C1, merkleRoot) off-circuit.
    // Uses Field constants — safe outside ZkProgram methods.
    console.log('\nComputing Merkle root and z off-circuit...');
    console.time('merkle-offcircuit');
    const { merkleRoot, z, zBigint } = computeMerkleRootOffCircuit(
        input.blobBigints, input.C0, input.C1
    );
    console.timeEnd('merkle-offcircuit');
    console.log('merkleRoot          :', merkleRoot.toBigInt().toString(16));
    console.log('z = Poseidon(C,root):', zBigint.toString(16));

    // FIX 2 — assert z ∉ domain before proving.
    // This guarantees evalChunk never inverts zero.
    if (ROOTS_SET.has(zBigint.toString())) {
        throw new Error('z is a domain point — this should never happen for a Poseidon challenge');
    }
    console.log('z ∉ domain          : true (asserted)');

    // FIX 1 — KZG point-opening check at the circuit's z
    const yBigint = evaluateBlobOffCircuit(input.blobBigints, zBigint);
    const zBytes = bigintToBytesBE(zBigint, BYTES_PER_FIELD) as Bytes32;
    const yBytes = bigintToBytesBE(yBigint, BYTES_PER_FIELD) as Bytes32;
    const [piZRaw] = computeKzgProof(input.blob, zBytes);
    const piZBytes = Uint8Array.from(piZRaw);
    const kzgVerify = verifyKzgProof(
        input.commitment, zBytes, yBytes, piZBytes as Bytes48
    );
    console.log('\n=== KZG point-opening at circuit z ===');
    console.log('z (circuit)         :', zBigint.toString(16));
    console.log('y (off-circuit)     :', yBigint.toString());
    console.log('KZG.verify(C,z,y,π) :', kzgVerify);  // must be true

    const C0 = Field(input.C0);
    const C1 = Field(input.C1);

    const blobChunks: BlsFrA[][] = Array.from({ length: NUM_CHUNKS }, (_, k) =>
        input.blobBigints.slice(k * CHUNK_SIZE, (k + 1) * CHUNK_SIZE).map(x => new BlsFrAlmost(x))
    );

    console.log('\nCompiling...');
    console.time('compile');
    const { verificationKey } = await BlobEvalProgram.compile({ cache });
    console.timeEnd('compile');

    console.log('\nProving...');
    console.time('prove-total');
    const proof = await proveTree(blobChunks, z, C0, C1);
    console.timeEnd('prove-total');

    console.log('\nVerifying...');
    console.time('verify');
    const ok = await verify(proof, verificationKey);
    console.timeEnd('verify');

    const output = proof.publicOutput;
    const yCircuit = output.partialSum.toBigInt();

    console.log('\n=== Circuit result ===');
    console.log('proof verified      :', ok);
    console.log('is finalized        :', output.chunksDone.toBigInt() === BigInt(FIELD_ELEMENTS_PER_BLOB + 1));
    console.log('y (circuit)         :', yCircuit.toString());
    console.log('y (off-circuit)     :', yBigint.toString());
    console.log('y circuit == off-c  :', yCircuit === yBigint);
    console.log('merkleRoot matches  :', output.merkleRoot.toBigInt() === merkleRoot.toBigInt());
    console.log('KZG.verify at z     :', kzgVerify);

    console.log('\n=== SP1 responsibilities ===');
    console.log('SP1 must prove:');
    console.log('  1. merkleRoot == PoseidonMerkle(blob)  [same leaf encoding]');
    console.log('  2. C_kzg == KZGCommit(blob)            [trusted setup]');
    console.log('  3. z == Poseidon(C0, C1, merkleRoot)   [recomputable from public output]');
    console.log('  4. KZG.verify(C_kzg, z, y, π_kzg)     [already checked above in JS]');
    console.log('Together: merkleRoot and C_kzg bind to the same blob, y = f(z) is correct.');

    if (!ok || !input.commitmentMatches || !input.proofVerifies || !kzgVerify)
        process.exitCode = 1;
}

main().catch(err => { console.error(err); process.exit(1); });