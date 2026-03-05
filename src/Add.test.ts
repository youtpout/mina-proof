import { AccountUpdate, Field, Mina, PrivateKey, PublicKey, VerificationKey } from 'o1js';
import { Add } from './Add.js';
import { AddZkProgram } from './AddZkProgram.js';
import { describe, it, before, beforeEach } from 'node:test';
import assert from 'node:assert';
import { writeFileSync, mkdirSync } from 'fs';
import { join } from 'path';
import { setBackend } from 'o1js';

/*
 * This file specifies how to test the `Add` example smart contract. It is safe to delete this file and replace
 * with your own tests.
 *
 * See https://docs.minaprotocol.com/zkapps for more info.
 */

const proofsEnabled = true;

// native prover
setBackend('native');

describe('Add', () => {
  let deployerAccount: Mina.TestPublicKey,
    deployerKey: PrivateKey,
    senderAccount: Mina.TestPublicKey,
    senderKey: PrivateKey,
    vk: VerificationKey,
    zkAppAddress: PublicKey,
    zkAppPrivateKey: PrivateKey,
    zkApp: Add;



  before(async () => {
    await AddZkProgram.compile({ proofsEnabled });
    vk = {
      data: "",
      hash: Field(0),
    };
    if (proofsEnabled) {
      let { verificationKey } = await Add.compile();
      vk = verificationKey;
      console.log('Verification key', vk);
    }
  });

  beforeEach(async () => {
    const Local = await Mina.LocalBlockchain({ proofsEnabled });
    Mina.setActiveInstance(Local);
    [deployerAccount, senderAccount] = Local.testAccounts;
    deployerKey = deployerAccount.key;
    senderKey = senderAccount.key;

    zkAppPrivateKey = PrivateKey.random();
    zkAppAddress = zkAppPrivateKey.toPublicKey();
    zkApp = new Add(zkAppAddress);
  });

  async function localDeploy() {
    const txn = await Mina.transaction(deployerAccount, async () => {
      AccountUpdate.fundNewAccount(deployerAccount);
      await zkApp.deploy();
    });
    await txn.prove();
    // this tx needs .sign(), because `deploy()` adds an account update that requires signature authorization
    await txn.sign([deployerKey, zkAppPrivateKey]).send();
  }

  it('initilaizes the  `AddZKprogram`', async () => {
    await localDeploy();

    const devnet = Mina.Network({
      // We need to default to the testnet networkId if none is specified for this deploy alias in config.json
      // This is to ensure the backward compatibility.
      networkId: "testnet",
      mina: "https://api.minascan.io/node/devnet/v1/graphql",
      archive: "https://api.minascan.io/archive/devnet/v1/graphql"
    })
    Mina.setActiveInstance(devnet);

    const { proof } = await AddZkProgram.init(Field(1));

    assert.deepStrictEqual(proof.publicOutput, Field(1));
  });

  it('correctly settles `AddZKprogram` state on the `Add` smart contract', async () => {
    await localDeploy();
    const initialState = zkApp.num.get();

    const init = await AddZkProgram.init(initialState);
    const update = await AddZkProgram.update(initialState, init.proof);

    console.log('proof', update.proof.toJSON());

    const outputDir = join(process.cwd(), 'build', 'proofs');
    mkdirSync(outputDir, { recursive: true });

    const proofPath = join(outputDir, 'proof.json');
    const metaPath = join(outputDir, 'proof.meta.json');
    const txnPath = join(outputDir, 'txn.json');

    const proofJson = update.proof.toJSON();
    writeFileSync(proofPath, JSON.stringify(proofJson, null, 2));

    const metadata = {
      timestamp: new Date().toISOString(),
      verificationKey: vk?.data,
      publicInput: proofJson.publicInput,
      publicOutput: proofJson.publicOutput,
      maxProofsVerified: proofJson.maxProofsVerified,
      verified: true,
      program: 'simple-proof',
    };

    writeFileSync(metaPath, JSON.stringify(metadata, null, 2));

    // settleState transaction
    const txn = await Mina.transaction(senderAccount, async () => {
      await zkApp.settleState(update.proof);
    });
    await txn.prove();
    await txn.sign([senderKey]).send();


    writeFileSync(txnPath, txn.toJSON());

    const updatedNum = zkApp.num.get();
    assert.deepStrictEqual(updatedNum, Field(1));
  });
});
