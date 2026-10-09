// Run after dune build @web/browser: node web/test.cjs
const assert = require('node:assert/strict');
const api = require('../_build/default/web/browser.bc.js').proofglyph;
const examples = JSON.parse(api.examples);
for (const { path, source } of examples) {
  const compiled = path.endsWith('.pg')
    ? { ok: true, output: source } : api.compileAt(path, source);
  assert.equal(compiled.ok, true, `${path}: ${compiled.output}`);
  const checked = api.check(compiled.output);
  assert.equal(checked.ok, true, `${path}: ${checked.output}`);
}
assert.equal(api.compileAt('examples/a.ht', 'import "missing.ht";').ok, false);
assert.equal(api.compileAt('examples/basics.ht', 'import "./basics.ht";').ok, false);
assert.equal(api.compileAt('examples/a.ht', 'import "../../outside.ht";').ok, false);
console.log(`All ${examples.length} examples passed; invalid imports rejected.`);

const catalog = require('../_build/default/web/catalog.json');
assert.ok(Object.values(catalog.proofs).some(matches =>
  matches.some(({name, path}) => name === 'fermat' && path === 'examples/commons/nat/fermat.ht')));
const sources = new Map(examples.map(({path, source}) => [path, source]));
for (const matches of Object.values(catalog.proofs)) {
  for (const {name, path, line} of matches) {
    assert.match(require('node:fs').readFileSync(require('node:path').join(__dirname, '..', path), 'utf8').split('\n')[line - 1],
      new RegExp(`^(theorem|def) ${name}\\b`));
  }
}
assert.ok(Object.values(catalog.proofs).some(matches => matches.length > 1));
assert.deepEqual(catalog, require('../examples/catalog.json'));
console.log('Catalog names and source locations passed.');

const fs = require('node:fs');
const document = fs.readFileSync(require('node:path').join(__dirname, '../docs/proofs.md'), 'utf8');
const startMarker = '<!-- proof-catalog:start -->';
const endMarker = '<!-- proof-catalog:end -->';
assert.equal(document.split(startMarker).length, 2);
assert.equal(document.split(endMarker).length, 2);
assert.ok(document.indexOf(startMarker) < document.indexOf(endMarker));
const documentedRows = document.split(startMarker)[1].split(endMarker)[0].split('\n')
  .filter(row => /^\|.*\[.*\]\(\.\.\/examples\//.test(row));
assert.deepEqual(Object.keys(catalog.proofs), documentedRows.map(row => {
  const [, subject, title] = row.split('|').map(cell => cell.trim());
  return `${subject}：${title.replaceAll('`', '')}`;
}));
console.log('Catalog matches the documented proofs table.');

const mapped = api.compileAt('examples/map.ht', 'axiom A : Type;\ndef id (x : A) : A := x;');
assert.equal(mapped.ok, true);
const map = JSON.parse(mapped.sourcemap).mappings;
assert.equal(map[1].name, 'id');
assert.equal(map[1].file, 'examples/map.ht');
assert.equal(map[1].line, 2);
assert.match(api.checkMapped(mapped.output).output, /id \[proven\] : \(forall \(\$x0 : A\), A\)/);
assert.match(api.check(mapped.output).output, /c1 \[proven\]/);
assert.match(api.checkMapped(mapped.output + '\n').output, /c1 \[proven\]/);
const invalid = api.compileAt('examples/map.ht', 'axiom A : Type;\ndef bad : A := Type;');
assert.equal(invalid.ok, false);
assert.match(invalid.output, /^error: examples\/map\.ht:2:1 \(bad\): byte \d+: proof type mismatch$/);
assert.match(api.checkMapped(mapped.output).output, /c1 \[proven\]/);
assert.equal(api.checkMapped('$0:').ok, false);
const imported = api.compileAt('examples/commons/nat/addition.ht', sources.get('examples/commons/nat/addition.ht'));
assert.match(api.checkMapped(imported.output).output, /add_comm \[proven\]/);
assert.ok(JSON.parse(imported.sourcemap).mappings.every(m => m.file === 'examples/commons/nat/addition.ht'));
for (const m of JSON.parse(imported.sourcemap).mappings) {
  assert.match(sources.get(m.file).split('\n')[m.line - 1], new RegExp(`^(axiom|def|theorem) ${m.name}\\b`));
}
for (const {path, source} of examples.filter(entry => entry.path.endsWith('.ht'))) {
  assert.doesNotMatch(source, /^\s*import\s/m, path);
  assert.equal(api.compileAt(path, source).ok, true, `${path} compiles without an import resolver`);
}
assert.match(api.compileAt('examples/a.ht', 'import \"commons/nat/addition.ht\";').output,
  /^error: examples\/a\.ht:1:1: imports require compile_file or load$/);
console.log('Sourcemap names, imported locations, errors and stale-map fallback passed.');

const {toLatex} = require('./math.source.js');
const katex = process.env.KATEX_TEST_MODULE ? require(process.env.KATEX_TEST_MODULE) : null;
let renderedTypes = 0;
for (const {path, source} of examples.filter(entry => entry.path.endsWith('.ht'))) {
  const compiled = api.compileAt(path, source);
  const entries = JSON.parse(api.checkMapped(compiled.output).entries);
  assert.ok(entries.every(entry => ['assumption', 'proven'].includes(entry.origin)));
  for (const entry of entries.filter(entry => entry.origin === 'proven')) {
    const {latex} = toLatex(entry.type);
    assert.ok(latex.length > 0, `${path}:${entry.name}`);
    assert.doesNotMatch(latex, /undefined|NaN/);
    if (katex) assert.ok(katex.renderToString(latex, {throwOnError: true, trust: false}).includes('<math'));
    renderedTypes++;
  }
}
function formula(path, name) {
  const compiled = api.compileAt(path, sources.get(path));
  const entry = JSON.parse(api.checkMapped(compiled.output).entries).find(entry => entry.name === name);
  return toLatex(entry.type).latex;
}
assert.equal(formula('examples/commons/nat/sums.ht', 'odd_sum_square'),
  String.raw`\forall n\in\mathbb{N},\; \sum_{k=0}^{n-1} \left(2 \cdot k+1\right) = {n}^2`);
assert.equal(formula('examples/commons/sets/russell.ht', 'no_universal_set'),
  String.raw`\neg \left(\exists x:U,\; \forall y:U,\; y \in x\right)`);
assert.equal(formula('examples/commons/nat/prime_infinitude.ht', 'primes_infinite'),
  String.raw`\forall n\in\mathbb{N},\; \exists m\in\mathbb{N},\; \mathrm{Prime}\left(m\right) \land n < m`);
assert.equal(formula('examples/basics.ht', 'id'), String.raw`A \to A`);
// Bound variables under two dependent binders must stay distinct.
assert.equal(toLatex(['pi', ['const', 'U'], ['pi', ['const', 'U'],
  ['app', ['app', ['const', 'Mem'], ['var', 1]], ['var', 0]]]]).latex,
  String.raw`\forall x:U,\; \forall y:U,\; x \in y`);
// Direct proofglyph edits lose mapped mathematical names, so retain generic kernel constants.
const raw = JSON.parse(api.check('*:#0#0>#0$0\\!').entries);
assert.equal(toLatex(raw[1].type).latex, String.raw`\mathrm{c0} \to \mathrm{c0}`);
console.log(`${renderedTypes} checked types formatted${katex ? ' and rendered with KaTeX' : ''}; formulas and binder scope passed.`);
assert.equal(toLatex(['app', ['app', ['const', 'Imp'],
  ['app', ['app', ['const', 'Imp'], ['const', 'A']], ['const', 'B']]], ['const', 'C']]).latex,
  String.raw`\left(A \to B\right) \to C`);
assert.equal(toLatex(['pi', ['const', 'Nat'], ['app', ['const', 'Prf'], ['const', 'P']]]).latex,
  String.raw`\forall n\in\mathbb{N},\; P`);
assert.equal(toLatex(['pi', ['const', 'U'], ['app', ['app', ['const', 'Mem'], ['var', 0]], ['const', 'x']]]).latex,
  String.raw`\forall y:U,\; y \in x`);
