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
import { randomBytes } from 'node:crypto';

setBackend('native');

// -----------------------------------------------------------------------------
// Constants
// -----------------------------------------------------------------------------

const BLS_MODULUS =
    52435875175126190479447740508185965837690552500527637822603658699938581184513n;

const FIELD_ELEMENTS_PER_BLOB = 4096;
const LOG2_BLOB_SIZE = 12;
const PRIMITIVE_ROOT_OF_UNITY = 7n;

const CHUNK_SIZE = 256;
const NUM_CHUNKS = FIELD_ELEMENTS_PER_BLOB / CHUNK_SIZE;

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
// Helpers
// -----------------------------------------------------------------------------

function mod(x: bigint): bigint {
    const r = x % BLS_MODULUS;
    return r >= 0n ? r : r + BLS_MODULUS;
}

function modPow(base: bigint, exp: bigint, m: bigint): bigint {
    let result = 1n;
    let b = base % m;
    let e = exp;

    while (e > 0n) {
        if (e & 1n) result = (result * b) % m;
        b = (b * b) % m;
        e >>= 1n;
    }

    return result;
}

function modInv(x: bigint): bigint {
    if (x === 0n) throw new Error('Division by zero');
    return modPow(mod(x), BLS_MODULUS - 2n, BLS_MODULUS);
}

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

// -----------------------------------------------------------------------------
// Roots
// -----------------------------------------------------------------------------

const ROOTS_BIGINT = bitReversalPermutation(computeRootsOfUnity(FIELD_ELEMENTS_PER_BLOB));
const ROOTS = ROOTS_BIGINT.map((x) => new BlsFrCanonical(x));
const ROOTS_SET = new Set(ROOTS_BIGINT.map((x) => x.toString()));

const CHUNK_ROOTS: BlsFrC[][] = Array.from({ length: NUM_CHUNKS }, (_, k) =>
    ROOTS.slice(k * CHUNK_SIZE, (k + 1) * CHUNK_SIZE)
);

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
// Prover tree
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
            const { proof } = await BlobEvalProgram.merge(
                level[i],
                level[i + 1]
            );

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
// Off-circuit reference
// -----------------------------------------------------------------------------

function evaluateBlobOffCircuit(blob: bigint[], z: bigint): bigint {
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

function randomBlsScalar(): bigint {
    while (true) {
        const x = BigInt(`0x${randomBytes(32).toString('hex')}`);
        if (x < BLS_MODULUS) return x;
    }
}

function randomBlob(): bigint[] {
    return Array.from({ length: FIELD_ELEMENTS_PER_BLOB }, () => randomBlsScalar());
}

function randomChallengeOutsideDomain(): bigint {
    while (true) {
        const z = randomBlsScalar();
        if (!ROOTS_SET.has(z.toString())) return z;
    }
}

// -----------------------------------------------------------------------------
// Main
// -----------------------------------------------------------------------------

async function main() {
    console.log('=== KZG Blob Eval — Single Leaf Method ===');
    console.log(`  methods    : leaf / merge / finalize`);
    console.log(`  chunks     : ${NUM_CHUNKS}`);
    console.log(`  chunk size : ${CHUNK_SIZE}\n`);

    console.time('generate-test-data');
    const blobBigints = randomBlob();
    const zBigint = randomChallengeOutsideDomain();
    const yBigint = evaluateBlobOffCircuit(blobBigints, zBigint);
    const CBigint = randomBlsScalar() % (2n ** 254n);
    console.timeEnd('generate-test-data');

    const z = new BlsFrCanonical(zBigint);
    const C = Field(CBigint);

    const blobChunks: BlsFrA[][] = Array.from({ length: NUM_CHUNKS }, (_, k) =>
        blobBigints
            .slice(k * CHUNK_SIZE, (k + 1) * CHUNK_SIZE)
            .map((x) => new BlsFrAlmost(x))
    );

    const chunkRoots: BlsFrC[][] = CHUNK_ROOTS;

    console.log('Compiling...');
    console.time('compile');
    const { verificationKey } = await BlobEvalProgram.compile({ cache });
    console.timeEnd('compile');
    console.log();

    console.log('Proving...');
    console.time('prove-total');
    const proof = await proveTree(blobChunks, chunkRoots, z, C);
    console.timeEnd('prove-total');
    console.log();

    console.time('verify');
    const ok = await verify(proof, verificationKey);
    console.timeEnd('verify');

    const output = proof.publicOutput;
    const yCircuit = output.partialSum.toBigInt();

    console.log('\n=== Result ===');
    console.log('proof verified :', ok);
    console.log(
        'is finalized   :',
        output.chunksDone.toBigInt() === BigInt(FIELD_ELEMENTS_PER_BLOB + 1)
    );
    console.log('z matches      :', output.z.toBigInt() === zBigint);
    console.log('C matches      :', output.C.toBigInt() === CBigint);
    console.log('y (circuit)    :', yCircuit);
    console.log('y (reference)  :', yBigint);
    console.log('y correct      :', yCircuit === yBigint);
}

main().catch((err) => {
    console.error(err);
    process.exit(1);
});