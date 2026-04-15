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
 * Inversion strategy (Gemini trick):
 *   Instead of computing inverses inside the circuit (expensive), we provide
 *   them as witnesses (off-circuit hints) and only verify d × inv = 1.
 *   Cost: 1 mul + 1 check per element vs ~60 rows for Montgomery batch inversion.
 *
 * Number of ZkProgram methods: 3 (leaf, merge, finalize).
 *   More methods → larger combined Kimchi index encoding → crash.
 *   ChunkRootsArray (256 × 3 limbs = 768 witness vars) is fine at this scale.
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
// CHUNK_SIZE=256 causes ~85k rows/leaf → SRS=2^17 → Kimchi index encoding overflows.
// CHUNK_SIZE=64 gives ~10k rows/leaf → SRS=2^14 → encoding ~10M elements, manageable.
const CHUNK_SIZE = 64;
const NUM_CHUNKS = FIELD_ELEMENTS_PER_BLOB / CHUNK_SIZE; // 64
const LOG2_CHUNK_SIZE = 6;  // log2(64)
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

// 3 methods total → ChunkRootsArray as private input is fine (768 witness vars)
const ChunkArray = Provable.Array(BlsFrAlmost, CHUNK_SIZE);
const ChunkRootsArray = Provable.Array(BlsFrCanonical, CHUNK_SIZE);

const WIDTH = new BlsFrCanonical(BigInt(FIELD_ELEMENTS_PER_BLOB));
const ONE = new BlsFrCanonical(1n);
const ONE_ALMOST = new BlsFrAlmost(1n); // for assertEquals in evalChunk
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
// C as two Fields — no bits dropped
// ---------------------------------------------------------------------------

function kzgCommitmentToVersionedHash(commitmentBytes: Uint8Array): Uint8Array {
    const hash = sha256(commitmentBytes);
    hash[0] = KZG_VERSION_BYTE;
    return hash;
}

function versionedHashToFields(versionedHash: Uint8Array): { C0: bigint; C1: bigint } {
    const full = bytesToBigintBE(versionedHash);
    return { C0: full >> 128n, C1: full & ((1n << 128n) - 1n) };
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
// Roots of unity
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
// Off-circuit evaluator — z ∉ domain asserted by caller
// ---------------------------------------------------------------------------

function evaluateBlobOffCircuit(blob: bigint[], z: bigint): bigint {
    let sum = 0n;
    for (let i = 0; i < FIELD_ELEMENTS_PER_BLOB; i++) {
        const den = mod(z - ROOTS_BIGINT[i]);
        sum = mod(sum + mod(mod(blob[i] * ROOTS_BIGINT[i]) * modInv(den)));
    }
    const scale = mod(mod(modPow(z, BigInt(FIELD_ELEMENTS_PER_BLOB), BLS_MODULUS) - 1n) * modInv(BigInt(FIELD_ELEMENTS_PER_BLOB)));
    return mod(scale * sum);
}

// ---------------------------------------------------------------------------
// Off-circuit Merkle root + z derivation — mirrors the circuit exactly
// ---------------------------------------------------------------------------

function computeMerkleRootOffCircuit(
    blobBigints: bigint[],
    C0: bigint,
    C1: bigint,
): { merkleRoot: Field; z: BlsFrC; zBigint: bigint } {
    // Each blob element → hash its 3 limbs → leaf
    // Mirrors chunkToSubMerkleRoot: Poseidon.hash(fi.value)
    const mask88 = (1n << 88n) - 1n;
    let leaves: Field[] = blobBigints.map(x =>
        Poseidon.hash([Field(x & mask88), Field((x >> 88n) & mask88), Field(x >> 176n)])
    );

    // Binary tree reduction — mirrors merge combining sub-roots
    while (leaves.length > 1) {
        const next: Field[] = [];
        for (let i = 0; i < leaves.length; i += 2)
            next.push(Poseidon.hash([leaves[i], leaves[i + 1]]));
        leaves = next;
    }
    const merkleRoot = leaves[0];

    const zField = Poseidon.hash([Field(C0), Field(C1), merkleRoot]);
    const zBigint = zField.toBigInt() % BLS_MODULUS;
    return { merkleRoot, z: new BlsFrCanonical(zBigint), zBigint };
}

// ---------------------------------------------------------------------------
// Input loading
// ---------------------------------------------------------------------------

function loadBlobJson(): BlobJson {
    if (!existsSync(BLOB_JSON_PATH)) throw new Error(`Missing blob.json: ${BLOB_JSON_PATH}`);
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
    const versionedHash = kzgCommitmentToVersionedHash(commitmentBytes);
    const { C0, C1 } = versionedHashToFields(versionedHash);

    const computedCommitmentBytes = Uint8Array.from(blobToKzgCommitment(blob));
    const commitmentMatches = equalBytes(computedCommitmentBytes, commitmentBytes);
    const proofVerifies = verifyBlobKzgProof(blob, commitment, proof);
    const proofBatchVerifies = verifyBlobKzgProofBatch([blob], [commitment], [proof]);
    const computedBlobProofBytes = Uint8Array.from(computeBlobKzgProof(blob, commitment));
    const blobProofMatches = equalBytes(computedBlobProofBytes, proofBytes);

    return {
        blobBytes, commitmentBytes, proofBytes, blobBigints,
        versionedHash, C0, C1, blob, commitment,
        computedCommitmentBytes, commitmentMatches,
        proofVerifies, proofBatchVerifies,
        computedBlobProofBytes, blobProofMatches,
    };
}

// ---------------------------------------------------------------------------
// Public output
// ---------------------------------------------------------------------------

class BlobEvalOutput extends Struct({
    C0: Field,          // high 128 bits of EIP-4844 versioned hash
    C1: Field,          // low  128 bits of EIP-4844 versioned hash
    merkleRoot: Field,          // Poseidon Merkle root of all 4096 blob elements
    z: BlsFrCanonical, // Poseidon(C0, C1, merkleRoot) — derived in finalize
    partialSum: BlsFrAlmost,    // y = f(z) after finalize
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

/**
 * Non-deterministic inversion (Gemini trick):
 *   - Compute inv = 1/d  OFF-circuit as a Provable.witness hint
 *   - Verify d × inv = 1 IN-circuit (just one mul + one equality check)
 *
 * Cost: ~30 rows per element vs ~60 rows for Montgomery batch inversion.
 *
 * z ∉ domain is asserted in main() before proving, so d = z - w_i ≠ 0.
 */
function evalChunk(chunk: BlsFrA[], chunkRoots: BlsFrC[], z: BlsFrC): BlsFrA {
    const nums = chunk.map((fi, i) =>
        fi.mul(chunkRoots[i]).assertAlmostReduced() as BlsFrA
    );

    const terms: BlsFrU[] = chunk.map((_, i) => {
        const d = z.sub(chunkRoots[i]).assertAlmostReduced() as BlsFrA;

        // Provide inverse as off-circuit witness
        const inv = Provable.witness(BlsFrAlmost, () =>
            new BlsFrAlmost(modInv(d.toBigInt()))
        );

        // Verify in-circuit: d × inv must equal 1
        // Use ONE_ALMOST (BlsFrAlmost) to match types — not BlsFrCanonical ONE
        d.mul(inv).assertAlmostReduced().assertEquals(ONE_ALMOST, 'evalChunk: d×inv ≠ 1');

        return nums[i].mul(inv);
    });

    return BlsFr.sum(terms, CHUNK_SIGNS).assertAlmostReduced() as BlsFrA;
}

/**
 * Poseidon Merkle sub-root for one chunk of CHUNK_SIZE blob elements.
 *
 * Leaf encoding: hash the 3 × 88-bit limbs of each BLS element.
 *   Poseidon.hash(fi.value) = Poseidon.hash([l0, l1, l2])
 *
 * Tree: LOG2_CHUNK_SIZE = 8 levels of pair-hashing → 255 hashes per chunk.
 * 16 chunks × 255 + 15 merge hashes = 4095 hashes total — matches Dankrad.
 */
function chunkToSubMerkleRoot(chunk: BlsFrA[]): Field {
    let leaves: Field[] = chunk.map(fi => Poseidon.hash(fi.value));

    for (let level = 0; level < LOG2_CHUNK_SIZE; level++) {
        const next: Field[] = [];
        for (let i = 0; i < leaves.length; i += 2)
            next.push(Poseidon.hash([leaves[i], leaves[i + 1]]));
        leaves = next;
    }
    return leaves[0];
}

// ---------------------------------------------------------------------------
// ZkProgram — 3 methods only (leaf / merge / finalize)
//
// Having more methods causes the Kimchi combined index encoding to overflow
// V8's array allocation limit (~2^30 elements).
// ---------------------------------------------------------------------------

const BlobEvalProgram = ZkProgram({
    name: 'blob-eval-4096-method1-merkle-binding',
    publicOutput: BlobEvalOutput,

    methods: {
        // ── leaf ────────────────────────────────────────────────────────
        leaf: {
            privateInputs: [BlsFrCanonical, Field, Field, ChunkRootsArray, ChunkArray],

            async method(
                z: BlsFrC,
                C0: Field,
                C1: Field,
                chunkRoots: BlsFrC[],
                chunk: BlsFrA[],
            ): Promise<{ publicOutput: BlobEvalOutput }> {
                const partialSum = evalChunk(chunk, chunkRoots, z);
                const merkleRoot = chunkToSubMerkleRoot(chunk);
                return {
                    publicOutput: new BlobEvalOutput({
                        C0, C1, merkleRoot, z,
                        partialSum,
                        chunksDone: Field(CHUNK_SIZE),
                    }),
                };
            },
        },

        // ── merge ───────────────────────────────────────────────────────
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

        // ── finalize ────────────────────────────────────────────────────
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

                // Re-derive z from public data — verifiable by anyone
                const zField = Poseidon.hash([root.C0, root.C1, root.merkleRoot]);

                // Assert the z carried through the proof equals the derived value.
                // Limb reconstruction: integer = l0 + l1·2^88 + l2·2^176
                const [l0, l1, l2] = root.z.value;
                l0.add(l1.mul(Field(2n ** 88n))).add(l2.mul(Field(2n ** 176n)))
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
        const { proof } = await BlobEvalProgram.leaf(z, C0, C1, CHUNK_ROOTS[k], blobChunks[k]);
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

    console.log('\n=== Blob-level c-kzg checks ===');
    console.log('commitment matches  :', input.commitmentMatches);
    console.log('blob proof verifies :', input.proofVerifies);
    console.log('batch verifies      :', input.proofBatchVerifies);
    console.log('blob proof matches  :', input.blobProofMatches);
    console.log('versioned hash      :', bytesToHex(input.versionedHash));
    console.log('C0 (high 128 bits)  :', input.C0.toString(16));
    console.log('C1 (low  128 bits)  :', input.C1.toString(16));

    console.log('\nComputing Merkle root and z off-circuit...');
    console.time('merkle-offcircuit');
    const { merkleRoot, z, zBigint } = computeMerkleRootOffCircuit(
        input.blobBigints, input.C0, input.C1
    );
    console.timeEnd('merkle-offcircuit');
    console.log('merkleRoot          :', merkleRoot.toBigInt().toString(16));
    console.log('z = Poseidon(C,root):', zBigint.toString(16));

    if (ROOTS_SET.has(zBigint.toString()))
        throw new Error('z is a domain point — should never happen for a Poseidon challenge');
    console.log('z ∉ domain          : true (asserted)');

    const yBigint = evaluateBlobOffCircuit(input.blobBigints, zBigint);
    const zBytes = bigintToBytesBE(zBigint, BYTES_PER_FIELD) as Bytes32;
    const yBytes = bigintToBytesBE(yBigint, BYTES_PER_FIELD) as Bytes32;
    const [piZRaw] = computeKzgProof(input.blob, zBytes);
    const kzgVerify = verifyKzgProof(
        input.commitment, zBytes, yBytes, Uint8Array.from(piZRaw) as Bytes48
    );
    console.log('\n=== KZG point-opening at circuit z ===');
    console.log('y (off-circuit)     :', yBigint.toString());
    console.log('KZG.verify(C,z,y,π) :', kzgVerify);

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
    console.log('  1. merkleRoot == PoseidonMerkle(blob)  [same leaf encoding]');
    console.log('  2. C_kzg == KZGCommit(blob)            [trusted setup]');
    console.log('  3. z == Poseidon(C0, C1, merkleRoot)   [recomputable from public output]');
    console.log('  4. KZG.verify(C_kzg, z, y, π_kzg)     [checked above]');

    if (!ok || !input.commitmentMatches || !input.proofVerifies || !kzgVerify)
        process.exitCode = 1;
}

main().catch(err => { console.error(err); process.exit(1); });