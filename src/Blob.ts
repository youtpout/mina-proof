import {
    Field,
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

setBackend('native');

// -----------------------------------------------------------------------------
// Constants
// -----------------------------------------------------------------------------

const BLS_MODULUS =
    52435875175126190479447740508185965837690552500527637822603658699938581184513n;

const LOG2_BLOB_SIZE = 12;
const PRIMITIVE_ROOT_OF_UNITY = 7n;

const BYTES_PER_FIELD = 32;
const CHUNK_SIZE = 256;
const NUM_CHUNKS = FIELD_ELEMENTS_PER_BLOB / CHUNK_SIZE;

const FIAT_SHAMIR_PROTOCOL_DOMAIN = Buffer.from('FSBLOBVERIFY_V1_', 'ascii');

const PROJECT_ROOT = process.cwd();
const BLOB_JSON_PATH = path.join(PROJECT_ROOT, 'blob.json');
const TRUSTED_SETUP_PATH = path.join(PROJECT_ROOT, 'trusted_setup.txt');

const cache = Cache.FileSystem('./cache');

// -----------------------------------------------------------------------------
// Foreign field
// -----------------------------------------------------------------------------

class BlsFr extends createForeignField(BLS_MODULUS) { }
class BlsFrAlmost extends BlsFr.AlmostReduced { }
class BlsFrCanonical extends BlsFr.Canonical { }

type BlsFrA = InstanceType<typeof BlsFrAlmost>;
type BlsFrC = InstanceType<typeof BlsFrCanonical>;
type BlsFrU = InstanceType<typeof BlsFr>;

const ChunkArray = Provable.Array(BlsFrAlmost, CHUNK_SIZE);
const ChunkRootsArray = Provable.Array(BlsFrCanonical, CHUNK_SIZE);

const WIDTH = new BlsFrCanonical(BigInt(FIELD_ELEMENTS_PER_BLOB));
const ONE = new BlsFrCanonical(1n);
const CHUNK_SIGNS = Array.from({ length: CHUNK_SIZE - 1 }, () => 1 as const) as (
    | 1
    | -1
)[];

// -----------------------------------------------------------------------------
// JSON input shape
// -----------------------------------------------------------------------------

type BlobJson = {
    blobHex: string;
    commitmentHex: string;
    proofHex: string;
};

// -----------------------------------------------------------------------------
// Basic helpers
// -----------------------------------------------------------------------------

function mod(x: bigint): bigint {
    const r = x % BLS_MODULUS;
    return r >= 0n ? r : r + BLS_MODULUS;
}

function modPow(base: bigint, exp: bigint, modulus: bigint): bigint {
    let result = 1n;
    let b = mod(base);
    let e = exp;

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

function strip0x(hex: string): string {
    return hex.startsWith('0x') ? hex.slice(2) : hex;
}

function hexToBytes(hex: string): Uint8Array {
    const clean = strip0x(hex);
    if (clean.length % 2 !== 0) {
        throw new Error('Hex string must have an even number of characters');
    }
    return Uint8Array.from(Buffer.from(clean, 'hex'));
}

function bytesToHex(bytes: Uint8Array): string {
    return `0x${Buffer.from(bytes).toString('hex')}`;
}

function bytesToBigintBE(bytes: Uint8Array): bigint {
    return BigInt(`0x${Buffer.from(bytes).toString('hex')}`);
}

function bigintToBytesBE(x: bigint, length: number): Uint8Array {
    const hex = x.toString(16).padStart(length * 2, '0');
    return Uint8Array.from(Buffer.from(hex, 'hex'));
}

function equalBytes(a: Uint8Array, b: Uint8Array): boolean {
    return Buffer.from(a).equals(Buffer.from(b));
}

function sha256Bytes(data: Uint8Array): Uint8Array {
    return Uint8Array.from(createHash('sha256').update(data).digest());
}

// -----------------------------------------------------------------------------
// Blob parsing
// -----------------------------------------------------------------------------

function blobBytesToFieldElements(blobBytes: Uint8Array): bigint[] {
    if (blobBytes.length !== BYTES_PER_BLOB) {
        throw new Error(
            `Invalid blob length: got ${blobBytes.length}, expected ${BYTES_PER_BLOB}`
        );
    }

    const out: bigint[] = new Array(FIELD_ELEMENTS_PER_BLOB);

    for (let i = 0; i < FIELD_ELEMENTS_PER_BLOB; i++) {
        const start = i * BYTES_PER_FIELD_ELEMENT;
        const end = start + BYTES_PER_FIELD_ELEMENT;
        const x = bytesToBigintBE(blobBytes.slice(start, end));

        if (x >= BLS_MODULUS) {
            throw new Error(`Blob field element ${i} is >= BLS_MODULUS`);
        }

        out[i] = x;
    }

    return out;
}

// -----------------------------------------------------------------------------
// Roots of unity in bit-reversal permutation
// -----------------------------------------------------------------------------

function reverseBits(n: number, order: number): number {
    const width = order.toString(2).length - 1;
    return Number.parseInt(
        n.toString(2).padStart(width, '0').split('').reverse().join(''),
        2
    );
}

function bitReversalPermutation<T>(seq: T[]): T[] {
    return seq.map((_, i) => seq[reverseBits(i, seq.length)]);
}

function computePowers(x: bigint, n: number): bigint[] {
    const out: bigint[] = [];
    let cur = 1n;

    for (let i = 0; i < n; i++) {
        out.push(cur);
        cur = mod(cur * x);
    }

    return out;
}

function computeRootsOfUnity(order: number): bigint[] {
    const root = modPow(
        PRIMITIVE_ROOT_OF_UNITY,
        (BLS_MODULUS - 1n) / BigInt(order),
        BLS_MODULUS
    );
    return computePowers(root, order);
}

const ROOTS_BIGINT = bitReversalPermutation(computeRootsOfUnity(FIELD_ELEMENTS_PER_BLOB));
const ROOTS = ROOTS_BIGINT.map((x) => new BlsFrCanonical(x));
const ROOTS_SET = new Set(ROOTS_BIGINT.map((x) => x.toString()));

const CHUNK_ROOTS: BlsFrC[][] = Array.from({ length: NUM_CHUNKS }, (_, k) =>
    ROOTS.slice(k * CHUNK_SIZE, (k + 1) * CHUNK_SIZE)
);

// -----------------------------------------------------------------------------
// Deneb z / y helpers
// -----------------------------------------------------------------------------

function hashToBlsField(data: Uint8Array): bigint {
    return bytesToBigintBE(sha256Bytes(data)) % BLS_MODULUS;
}

function computeChallengeFromBlobAndCommitment(
    blobBytes: Uint8Array,
    commitmentBytes: Uint8Array
): bigint {
    if (blobBytes.length !== BYTES_PER_BLOB) {
        throw new Error(
            `Invalid blob length: got ${blobBytes.length}, expected ${BYTES_PER_BLOB}`
        );
    }

    if (commitmentBytes.length !== BYTES_PER_COMMITMENT) {
        throw new Error(
            `Invalid commitment length: got ${commitmentBytes.length}, expected ${BYTES_PER_COMMITMENT}`
        );
    }

    const degreeBytes = bigintToBytesBE(BigInt(FIELD_ELEMENTS_PER_BLOB), 16);

    const transcript = Buffer.concat([
        FIAT_SHAMIR_PROTOCOL_DOMAIN,
        Buffer.from(degreeBytes),
        Buffer.from(blobBytes),
        Buffer.from(commitmentBytes),
    ]);

    return hashToBlsField(transcript);
}

function evaluateBlobOffCircuit(blob: bigint[], z: bigint): bigint {
    const evalIndex = ROOTS_BIGINT.findIndex((w) => w === z);
    if (evalIndex !== -1) {
        return blob[evalIndex];
    }

    let sum = 0n;

    for (let i = 0; i < FIELD_ELEMENTS_PER_BLOB; i++) {
        const num = mod(blob[i] * ROOTS_BIGINT[i]);
        const den = mod(z - ROOTS_BIGINT[i]);
        sum = mod(sum + mod(num * modInv(den)));
    }

    const zPowN = modPow(z, BigInt(FIELD_ELEMENTS_PER_BLOB), BLS_MODULUS);
    const scale = mod(mod(zPowN - 1n) * modInv(BigInt(FIELD_ELEMENTS_PER_BLOB)));

    return mod(scale * sum);
}

// -----------------------------------------------------------------------------
// Input loading
// -----------------------------------------------------------------------------

function loadBlobJson(): BlobJson {
    if (!existsSync(BLOB_JSON_PATH)) {
        throw new Error(`Missing blob.json at project root: ${BLOB_JSON_PATH}`);
    }

    const raw = readFileSync(BLOB_JSON_PATH, 'utf8');
    const parsed = JSON.parse(raw) as Partial<BlobJson>;

    if (!parsed.blobHex || !parsed.commitmentHex || !parsed.proofHex) {
        throw new Error('blob.json must contain blobHex, commitmentHex, and proofHex');
    }

    return {
        blobHex: parsed.blobHex,
        commitmentHex: parsed.commitmentHex,
        proofHex: parsed.proofHex,
    };
}

function loadBlobscanCase() {
    const { blobHex, commitmentHex, proofHex } = loadBlobJson();

    const blobBytes = hexToBytes(blobHex);
    const commitmentBytes = hexToBytes(commitmentHex);
    const proofBytes = hexToBytes(proofHex);

    if (blobBytes.length !== BYTES_PER_BLOB) {
        throw new Error(
            `blobHex must decode to ${BYTES_PER_BLOB} bytes, got ${blobBytes.length}`
        );
    }

    if (commitmentBytes.length !== BYTES_PER_COMMITMENT) {
        throw new Error(
            `commitmentHex must decode to ${BYTES_PER_COMMITMENT} bytes, got ${commitmentBytes.length}`
        );
    }

    if (proofBytes.length !== BYTES_PER_PROOF) {
        throw new Error(
            `proofHex must decode to ${BYTES_PER_PROOF} bytes, got ${proofBytes.length}`
        );
    }

    const blob = blobBytes as Blob;
    const commitment = commitmentBytes as Bytes48;
    const proof = proofBytes as Bytes48;

    const blobBigints = blobBytesToFieldElements(blobBytes);
    const zBigint = computeChallengeFromBlobAndCommitment(
        blobBytes,
        commitmentBytes
    );
    const yBigint = evaluateBlobOffCircuit(blobBigints, zBigint);

    const computedCommitmentBytes = Uint8Array.from(blobToKzgCommitment(blob));
    const commitmentMatches = equalBytes(computedCommitmentBytes, commitmentBytes);

    const proofVerifies = verifyBlobKzgProof(blob, commitment, proof);
    const proofBatchVerifies = verifyBlobKzgProofBatch([blob], [commitment], [proof]);

    const computedBlobProofBytes = Uint8Array.from(
        computeBlobKzgProof(blob, commitment)
    );
    const blobProofMatches = equalBytes(computedBlobProofBytes, proofBytes);

    const zBytes = bigintToBytesBE(zBigint, BYTES_PER_FIELD) as Bytes32;
    const [proofAtZRaw, yBytesRaw] = computeKzgProof(blob, zBytes);
    const proofAtZBytes = Uint8Array.from(proofAtZRaw);
    const yBytes = Uint8Array.from(yBytesRaw);
    const yFromCkzgBigint = bytesToBigintBE(yBytes);

    const verifyAtZ = verifyKzgProof(
        commitment,
        zBytes,
        yBytes as Bytes32,
        proofAtZBytes as Bytes48
    );

    const yMatchesCkzg = yFromCkzgBigint === yBigint;

    const commitmentTagBytes = sha256Bytes(commitmentBytes).slice(0, 31);
    const CBigint = bytesToBigintBE(commitmentTagBytes);

    return {
        blobBytes,
        commitmentBytes,
        proofBytes,
        blobBigints,
        zBigint,
        yBigint,
        CBigint,
        computedCommitmentBytes,
        commitmentMatches,
        proofVerifies,
        proofBatchVerifies,
        computedBlobProofBytes,
        blobProofMatches,
        zBytes,
        proofAtZBytes,
        yBytes,
        yFromCkzgBigint,
        yMatchesCkzg,
        verifyAtZ,
    };
}

// -----------------------------------------------------------------------------
// Public output
// -----------------------------------------------------------------------------

class BlobEvalOutput extends Struct({
    z: BlsFrCanonical,
    C: Field,
    partialSum: BlsFrAlmost,
    chunksDone: Field,
}) { }

// -----------------------------------------------------------------------------
// Circuit helpers
// -----------------------------------------------------------------------------

function squareRepeatedly(x: BlsFrA | BlsFrC, rounds: number): BlsFrA {
    let acc = x as unknown as BlsFrA;

    for (let i = 0; i < rounds; i++) {
        acc = acc.mul(acc).assertAlmostReduced() as BlsFrA;
    }

    return acc;
}

function batchInvert(xs: BlsFrA[]): BlsFrA[] {
    const n = xs.length;
    if (n === 0) return [];
    if (n === 1) return [xs[0].inv().assertAlmostReduced() as BlsFrA];

    const prefix = new Array<BlsFrA>(n);
    prefix[0] = xs[0];

    for (let i = 1; i < n; i++) {
        prefix[i] = prefix[i - 1].mul(xs[i]).assertAlmostReduced() as BlsFrA;
    }

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

function evalChunk(chunk: BlsFrA[], chunkRoots: BlsFrC[], z: BlsFrC): BlsFrA {
    const nums = chunk.map(
        (fi, i) => fi.mul(chunkRoots[i]).assertAlmostReduced() as BlsFrA
    );

    const dens = chunkRoots.map(
        (w) => z.sub(w).assertAlmostReduced() as BlsFrA
    );

    const invs = batchInvert(dens);
    const terms = nums.map((n, i) => n.mul(invs[i])) as BlsFrU[];

    return BlsFr.sum(terms, CHUNK_SIGNS).assertAlmostReduced() as BlsFrA;
}

// -----------------------------------------------------------------------------
// ZkProgram
// -----------------------------------------------------------------------------

const BlobEvalProgram = ZkProgram({
    name: 'blob-eval-4096-tree-single-leaf',
    publicOutput: BlobEvalOutput,

    methods: {
        leaf: {
            privateInputs: [BlsFrCanonical, Field, ChunkRootsArray, ChunkArray],

            async method(
                z: BlsFrC,
                C: Field,
                chunkRoots: BlsFrC[],
                chunk: BlsFrA[]
            ): Promise<{ publicOutput: BlobEvalOutput }> {
                const partialSum = evalChunk(chunk, chunkRoots, z);

                return {
                    publicOutput: new BlobEvalOutput({
                        z,
                        C,
                        partialSum,
                        chunksDone: Field(CHUNK_SIZE),
                    }),
                };
            },
        },

        merge: {
            privateInputs: [SelfProof, SelfProof] as const,

            async method(
                leftProof: SelfProof<undefined, BlobEvalOutput>,
                rightProof: SelfProof<undefined, BlobEvalOutput>
            ): Promise<{ publicOutput: BlobEvalOutput }> {
                leftProof.verify();
                rightProof.verify();

                const l = leftProof.publicOutput;
                const r = rightProof.publicOutput;

                l.z.assertEquals(r.z, 'merge: z mismatch');
                l.C.assertEquals(r.C, 'merge: C mismatch');

                const combinedSum = l.partialSum
                    .add(r.partialSum)
                    .assertAlmostReduced() as BlsFrA;

                const combinedChunks = l.chunksDone.add(r.chunksDone);

                return {
                    publicOutput: new BlobEvalOutput({
                        z: l.z,
                        C: l.C,
                        partialSum: combinedSum,
                        chunksDone: combinedChunks,
                    }),
                };
            },
        },

        finalize: {
            privateInputs: [SelfProof] as const,

            async method(
                rootProof: SelfProof<undefined, BlobEvalOutput>
            ): Promise<{ publicOutput: BlobEvalOutput }> {
                rootProof.verify();

                const root = rootProof.publicOutput;

                root.chunksDone.assertEquals(
                    Field(FIELD_ELEMENTS_PER_BLOB),
                    'finalize: tree does not cover the full blob'
                );

                const zPowN = squareRepeatedly(root.z, LOG2_BLOB_SIZE);
                const scale = zPowN.sub(ONE).assertAlmostReduced().div(WIDTH);
                const y = scale.mul(root.partialSum).assertAlmostReduced() as BlsFrA;

                return {
                    publicOutput: new BlobEvalOutput({
                        z: root.z,
                        C: root.C,
                        partialSum: y,
                        chunksDone: Field(FIELD_ELEMENTS_PER_BLOB + 1),
                    }),
                };
            },
        },
    },
});

class BlobEvalProof extends ZkProgram.Proof(BlobEvalProgram) { }

// -----------------------------------------------------------------------------
// Sequential recursion
// -----------------------------------------------------------------------------

async function proveTree(
    blobChunks: BlsFrA[][],
    chunkRoots: BlsFrC[][],
    z: BlsFrC,
    C: Field
): Promise<BlobEvalProof> {
    console.log(`  [level 0] proving ${NUM_CHUNKS} leaves sequentially...`);
    console.time('  level-0');

    const leaves: BlobEvalProof[] = [];

    for (let k = 0; k < NUM_CHUNKS; k++) {
        const { proof } = await BlobEvalProgram.leaf(
            z,
            C,
            chunkRoots[k],
            blobChunks[k]
        );

        leaves.push(proof as BlobEvalProof);
        console.log(`    leaf ${k + 1}/${NUM_CHUNKS} done`);
    }

    console.timeEnd('  level-0');

    let level: BlobEvalProof[] = leaves;
    let depth = 1;

    while (level.length > 1) {
        console.log(
            `  [level ${depth}] merging ${level.length / 2} pairs sequentially...`
        );
        console.time(`  level-${depth}`);

        const nextLevel: BlobEvalProof[] = [];

        for (let i = 0; i < level.length; i += 2) {
            const { proof } = await BlobEvalProgram.merge(level[i], level[i + 1]);

            nextLevel.push(proof as BlobEvalProof);
            console.log(`    merge ${i / 2 + 1}/${level.length / 2} done`);
        }

        level = nextLevel;
        console.timeEnd(`  level-${depth}`);
        depth++;
    }

    console.log('  [finalize]...');
    console.time('  finalize');

    const { proof } = await BlobEvalProgram.finalize(level[0]);

    console.timeEnd('  finalize');

    return proof as BlobEvalProof;
}

// -----------------------------------------------------------------------------
// Main
// -----------------------------------------------------------------------------

async function main() {
    console.log('=== KZG Blob Eval — Blobscan Check ===');
    console.log(`  methods    : leaf / merge / finalize`);
    console.log(`  chunks     : ${NUM_CHUNKS}`);
    console.log(`  chunk size : ${CHUNK_SIZE}\n`);

    if (ROOTS_SET.size !== FIELD_ELEMENTS_PER_BLOB) {
        throw new Error('Invalid roots-of-unity precomputation');
    }

    if (!existsSync(TRUSTED_SETUP_PATH)) {
        throw new Error(
            `Missing trusted_setup.txt at project root: ${TRUSTED_SETUP_PATH}`
        );
    }

    loadTrustedSetup(0, TRUSTED_SETUP_PATH);

    console.time('load-blobscan-input');
    const input = loadBlobscanCase();
    console.timeEnd('load-blobscan-input');

    console.log('\n=== Blobscan / c-kzg checks ===');
    console.log('blob bytes length        :', input.blobBytes.length);
    console.log('commitment bytes length  :', input.commitmentBytes.length);
    console.log('proof bytes length       :', input.proofBytes.length);
    console.log('commitment matches       :', input.commitmentMatches);
    console.log('blob proof verifies      :', input.proofVerifies);
    console.log('batch proof verifies     :', input.proofBatchVerifies);
    console.log('blob proof matches       :', input.blobProofMatches);
    console.log('verify at z              :', input.verifyAtZ);
    console.log('y matches c-kzg          :', input.yMatchesCkzg);
    console.log('computed commitment hex  :', bytesToHex(input.computedCommitmentBytes));
    console.log('input commitment hex     :', bytesToHex(input.commitmentBytes));
    console.log('computed blob proof hex  :', bytesToHex(input.computedBlobProofBytes));
    console.log('input blob proof hex     :', bytesToHex(input.proofBytes));
    console.log('proof at z hex           :', bytesToHex(input.proofAtZBytes));
    console.log('z (manual deneb)         :', input.zBigint.toString());
    console.log('y (manual deneb)         :', input.yBigint.toString());
    console.log('y (c-kzg at z)           :', input.yFromCkzgBigint.toString());

    const z = new BlsFrCanonical(input.zBigint);
    const C = Field(input.CBigint);

    const blobChunks: BlsFrA[][] = Array.from({ length: NUM_CHUNKS }, (_, k) =>
        input.blobBigints
            .slice(k * CHUNK_SIZE, (k + 1) * CHUNK_SIZE)
            .map((x) => new BlsFrAlmost(x))
    );

    const chunkRoots: BlsFrC[][] = CHUNK_ROOTS;

    console.log('\nCompiling...');
    console.time('compile');
    const { verificationKey } = await BlobEvalProgram.compile({ cache });
    console.timeEnd('compile');

    console.log('\nProving...');
    console.time('prove-total');
    const proof = await proveTree(blobChunks, chunkRoots, z, C);
    console.timeEnd('prove-total');

    console.log('\nVerifying recursive proof...');
    console.time('verify');
    const ok = await verify(proof, verificationKey);
    console.timeEnd('verify');

    const output = proof.publicOutput;
    const yCircuit = output.partialSum.toBigInt();

    console.log('\n=== Circuit result ===');
    console.log('proof verified           :', ok);
    console.log(
        'is finalized             :',
        output.chunksDone.toBigInt() === BigInt(FIELD_ELEMENTS_PER_BLOB + 1)
    );
    console.log('z matches manual         :', output.z.toBigInt() === input.zBigint);
    console.log('C matches tag            :', output.C.toBigInt() === input.CBigint);
    console.log('y (circuit)              :', yCircuit.toString());
    console.log('y (manual deneb)         :', input.yBigint.toString());
    console.log('y (c-kzg at z)           :', input.yFromCkzgBigint.toString());
    console.log('y circuit == manual      :', yCircuit === input.yBigint);
    console.log('y manual == c-kzg        :', input.yBigint === input.yFromCkzgBigint);
    console.log('y circuit == c-kzg       :', yCircuit === input.yFromCkzgBigint);

    if (
        !ok ||
        !input.commitmentMatches ||
        !input.verifyAtZ ||
        !input.yMatchesCkzg
    ) {
        process.exitCode = 1;
    }
}

main().catch((err) => {
    console.error(err);
    process.exit(1);
});