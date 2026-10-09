// Run after dune build @web/browser: node web/test.cjs
const assert = require('node:assert/strict');
const api = require('../_build/default/web/browser.bc.js').tinyprover;
const examples = JSON.parse(api.examples);
for (const { path, source } of examples) {
  const compiled = path.endsWith('.pa')
    ? { ok: true, output: source } : api.compileAt(path, source);
  assert.equal(compiled.ok, true, `${path}: ${compiled.output}`);
  const checked = api.check(compiled.output);
  assert.equal(checked.ok, true, `${path}: ${checked.output}`);
}
assert.equal(api.compileAt('examples/a.tp', 'import "missing.tp";').ok, false);
assert.equal(api.compileAt('examples/basics.tp', 'import "./basics.tp";').ok, false);
assert.equal(api.compileAt('examples/a.tp', 'import "../../outside.tp";').ok, false);
console.log(`All ${examples.length} examples passed; invalid imports rejected.`);

const catalog = require('../_build/default/web/catalog.json');
assert.ok(Object.values(catalog.proofs).some(matches =>
  matches.some(({name, path}) => name === 'fermat' && path === 'examples/commons/nat/fermat.tp')));
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

const mapped = api.compileAt('examples/map.tp', 'axiom A : Type;\ndef id (x : A) : A := x;');
assert.equal(mapped.ok, true);
const map = JSON.parse(mapped.sourcemap).mappings;
assert.equal(map[1].name, 'id');
assert.equal(map[1].file, 'examples/map.tp');
assert.equal(map[1].line, 2);
assert.match(api.checkMapped(mapped.output).output, /id \[proven\] : \(forall \(\$x0 : A\), A\)/);
assert.match(api.check(mapped.output).output, /c1 \[proven\]/);
assert.match(api.checkMapped(mapped.output + '\n').output, /c1 \[proven\]/);
const invalid = api.compileAt('examples/map.tp', 'axiom A : Type;\ndef bad : A := Type;');
assert.equal(invalid.ok, false);
assert.match(invalid.output, /^error: examples\/map\.tp:2:1 \(bad\): byte \d+: proof type mismatch$/);
assert.match(api.checkMapped(mapped.output).output, /c1 \[proven\]/);
assert.equal(api.checkMapped('$0:').ok, false);
const imported = api.compileAt('examples/commons/nat/addition.tp', sources.get('examples/commons/nat/addition.tp'));
assert.match(api.checkMapped(imported.output).output, /add_comm \[proven\]/);
assert.ok(JSON.parse(imported.sourcemap).mappings.every(m => m.file === 'examples/commons/nat/addition.tp'));
for (const m of JSON.parse(imported.sourcemap).mappings) {
  assert.match(sources.get(m.file).split('\n')[m.line - 1], new RegExp(`^(axiom|def|theorem) ${m.name}\\b`));
}
for (const {path, source} of examples.filter(entry => entry.path.endsWith('.tp'))) {
  assert.doesNotMatch(source, /^\s*import\s/m, path);
  assert.equal(api.compileAt(path, source).ok, true, `${path} compiles without an import resolver`);
}
assert.match(api.compileAt('examples/a.tp', 'import \"commons/nat/addition.tp\";').output,
  /^error: examples\/a\.tp:1:1: imports require compile_file or load$/);
console.log('Sourcemap names, imported locations, errors and stale-map fallback passed.');
