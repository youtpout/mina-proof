/**
 * Benchmark — rows count only via analyzeMethods(), no compile
 *
 * analyzeMethods() synthesizes the constraint system without generating
 * the proving key — no crash, gives the row count in seconds.
 *
 * We measure:
 *   A) Poseidon Merkle over 4096 leaves       → already known: 49 141 rows
 *   B) FF ops for one chunk of 256 elements   → extrapolate ×16 for full blob
 *   C) FF ops for all 4096 elements monolithic → real number if RAM allows
 */

import {
    Field,
    Poseidon,
    Provable,
    Struct,
    ZkProgram,
    createForeignField,
    setBackend,
} from 'o1js';
import { randomBytes } from 'node:crypto';

setBackend('native');

const BLS_MODULUS =
    52435875175126190479447740508185965837690552500527637822603658699938581184513n;

class BlsFr extends createForeignField(BLS_MODULUS) { }
class BlsFrAlmost extends BlsFr.AlmostReduced { }
class BlsFrCanonical extends BlsFr.Canonical { }

type BlsFrA = InstanceType<typeof BlsFrAlmost>;
type BlsFrC = InstanceType<typeof BlsFrCanonical>;
type BlsFrU = InstanceType<typeof BlsFr>;

// ---------------------------------------------------------------------------
// A) Merkle tree — 4096 leaves, 4095 Poseidon hashes
// ---------------------------------------------------------------------------

const LEAVES_COUNT = 4096;
const LeavesArray = Provable.Array(Field, LEAVES_COUNT);

function merkleLevel(nodes: Field[]): Field[] {
    const out: Field[] = [];
    for (let i = 0; i < nodes.length; i += 2)
        out.push(Poseidon.hash([nodes[i], nodes[i + 1]]));
    return out;
}

function merkleRoot(leaves: Field[]): Field {
    let level = leaves;
    while (level.length > 1) level = merkleLevel(level);
    return level[0];
}

const MerkleProgram = ZkProgram({
    name: 'bench-merkle',
    publicOutput: Field,
    methods: {
        computeRoot: {
            privateInputs: [LeavesArray],
            async method(leaves: Field[]): Promise<{ publicOutput: Field }> {
                return { publicOutput: merkleRoot(leaves) };
            },
        },
    },
});

// ---------------------------------------------------------------------------
// B) FF ops — single chunk of 256 elements (representative slice)
//    Rows × 16 = cost for full blob
// ---------------------------------------------------------------------------

const CHUNK_SIZE = 256;
const CHUNK_SIGNS = Array.from({ length: CHUNK_SIZE - 1 }, (): 1 => 1) as (1 | -1)[];
const ChunkArr = Provable.Array(BlsFrAlmost, CHUNK_SIZE);
const ChunkRootArr = Provable.Array(BlsFrCanonical, CHUNK_SIZE);

function batchInvert(xs: BlsFrA[]): BlsFrA[] {
    const n = xs.length;
    if (n === 1) return [xs[0].inv().assertAlmostReduced() as BlsFrA];
    const prefix = new Array<BlsFrA>(n);
    prefix[0] = xs[0];
    for (let i = 1; i < n; i++)
        prefix[i] = prefix[i - 1].mul(xs[i]).assertAlmostReduced() as BlsFrA;
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

const OneChunkProgram = ZkProgram({
    name: 'bench-ff-one-chunk',
    publicOutput: BlsFrAlmost,
    methods: {
        evalOneChunk: {
            privateInputs: [BlsFrCanonical, ChunkArr, ChunkRootArr],
            async method(
                z: BlsFrC,
                chunk: BlsFrA[],
                roots: BlsFrC[],
            ): Promise<{ publicOutput: BlsFrAlmost }> {
                const nums = chunk.map((fi, i) => fi.mul(roots[i]).assertAlmostReduced() as BlsFrA);
                const dens = roots.map(w => z.sub(w).assertAlmostReduced() as BlsFrA);
                const invs = batchInvert(dens);
                const terms = nums.map((n, i) => n.mul(invs[i])) as BlsFrU[];
                const sum = BlsFr.sum(terms, CHUNK_SIGNS).assertAlmostReduced() as BlsFrAlmost;
                return { publicOutput: sum };
            },
        },
    },
});

// ---------------------------------------------------------------------------
// Main — analyzeMethods only, no compile, no crash
// ---------------------------------------------------------------------------

async function main() {
    console.log('=== Benchmark: row counts via analyzeMethods() ===\n');

    // A) Merkle
    console.log('Analysing Merkle (4095 Poseidon hashes)...');
    console.time('analyze-merkle');
    const merkle = await MerkleProgram.analyzeMethods();
    console.timeEnd('analyze-merkle');
    const merkleRows = merkle.computeRoot.rows;
    console.log(`  rows: ${merkleRows}\n`);

    // B) One FF chunk
    console.log('Analysing FF ops (1 chunk = 256 elements)...');
    console.time('analyze-ff-chunk');
    const ffChunk = await OneChunkProgram.analyzeMethods();
    console.timeEnd('analyze-ff-chunk');
    const chunkRows = ffChunk.evalOneChunk.rows;
    const blobRows = chunkRows * 16; // extrapolation for 4096 elements
    console.log(`  rows per chunk (256 elems): ${chunkRows}`);
    console.log(`  extrapolated × 16 (4096 elems): ${blobRows}\n`);

    // Summary
    console.log('=== Summary ===');
    console.log(`Merkle rows (Method 1 overhead) : ${merkleRows.toLocaleString()}`);
    console.log(`FF ops rows (both methods)      : ${blobRows.toLocaleString()}`);
    console.log(`Method 1 total (Merkle + FF)    : ${(merkleRows + blobRows).toLocaleString()}`);
    console.log(`Method 2 total (FF only)        : ${blobRows.toLocaleString()}`);
    console.log();
    console.log(`Merkle overhead vs FF ops: ${((merkleRows / blobRows) * 100).toFixed(1)}%`);
    console.log();
    console.log('Note: rows × 16 is an extrapolation. The monolithic circuit may differ');
    console.log('slightly due to cross-chunk shared constraints, but the order of magnitude');
    console.log('is reliable for the Method 1 vs Method 2 decision.');
}

main().catch(err => { console.error(err); process.exit(1); });