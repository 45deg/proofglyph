// Run after dune build @web/browser: node web/worker.test.cjs
const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');
const vm = require('node:vm');
const {Worker} = require('node:worker_threads');
const output = path.resolve(__dirname, '../_build/default/web');

// Execute the actual browser worker scripts in a separate thread, with only
// the browser messaging/importScripts primitives adapted for Node.
class BrowserWorker {
  constructor(script) {
    this.thread = new Worker(`
      const {parentPort, workerData} = require('node:worker_threads');
      const fs = require('node:fs');
      const path = require('node:path');
      const vm = require('node:vm');
      const scope = vm.createContext({console, TextEncoder, TextDecoder,
        setTimeout, clearTimeout, postMessage: value => parentPort.postMessage(value)});
      scope.self = scope;
      scope.importScripts = file => vm.runInContext(
        fs.readFileSync(path.join(workerData.output, file), 'utf8'), scope);
      scope.importScripts(workerData.script);
      parentPort.on('message', data => scope.onmessage({data}));
    `, {eval: true, workerData: {output, script}});
    this.thread.on('message', data => this.onmessage?.({data}));
    this.thread.on('error', error => this.onerror?.({message: error.message, preventDefault() {}}));
  }
  postMessage(data) { this.thread.postMessage(data); }
  terminate() { this.thread.terminate(); }
}
const context = vm.createContext({Worker: BrowserWorker});
vm.runInContext(fs.readFileSync(path.join(output, 'worker-client.js'), 'utf8'), context);
const client = vm.runInContext('new ProofglyphWorker()', context);
async function main() {
  try {
    const {examples} = await client.request({kind: 'examples'});
    assert.ok(JSON.parse(examples).length > 0);
    const files = JSON.stringify([
      {path: 'examples/worker.ht', source: 'import "worker-base.ht"; theorem t : A := a;'},
      {path: 'examples/worker-base.ht', source: 'symbol A : Type; axiom a : A;'}
    ]);
    const compiled = await client.request({kind: 'compile', path: 'examples/worker.ht', files});
    assert.equal(compiled.compiled.ok, true);
    assert.equal(compiled.checked.ok, true);
    assert.equal(JSON.parse(compiled.files.output).length, 2);
    assert.equal(JSON.parse(compiled.checked.entries).at(-1).name, 't');
    const mapped = await client.request({kind: 'check', mapped: true, source: compiled.compiled.output});
    assert.equal(JSON.parse(mapped.checked.entries).at(-1).name, 't');
    const invalid = await client.request({kind: 'compile', path: 'examples/worker.ht', files: '[]'});
    assert.equal(invalid.compiled.ok, false);
    const rejected = await client.request({kind: 'check', source: '!'});
    assert.equal(rejected.checked.ok, false);
    await assert.rejects(client.request({kind: 'unknown'}), /Unknown operation/);

    // Cancellation rejects pending work and the next request starts a new worker.
    const previous = client.worker;
    const pending = client.request({kind: 'compile', path: 'examples/worker.ht', files});
    client.cancel();
    await assert.rejects(pending, /Operation cancelled/);
    assert.equal(client.worker, null);
    const retry = await client.request({kind: 'compile', path: 'examples/worker.ht', files});
    assert.notEqual(client.worker, previous);
    assert.equal(retry.checked.ok, true);
    console.log('Worker compilation, imports, mapped checking, errors, cancellation and restart passed.');
  } finally {
    client.worker?.terminate();
  }
}
main().catch(error => { console.error(error); process.exitCode = 1; });
