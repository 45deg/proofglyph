// Run with node web/i18n.test.cjs (no additional dependencies).
// Optionally pass a built/published web directory to validate the shipped assets.
const assert = require('node:assert/strict');
const fs = require('node:fs');
const vm = require('node:vm');
const path = require('node:path');
const shipped = process.argv[2] && path.resolve(process.argv[2]);
const asset = name => shipped ? path.join(shipped, name)
  : path.join(__dirname, name.replace(/\.(js|html)$/, '.source.$1'));
function loadScript(name, require) {
  const context = {module: {exports: {}}, require};
  vm.runInNewContext(fs.readFileSync(asset(name), 'utf8'), context);
  return context.module.exports;
}
const translations = loadScript('translations.js');
const {negotiate, create} = loadScript('i18n.js', () => translations);
assert.equal(negotiate(['ja-JP', 'en-US']), 'ja');
assert.equal(negotiate(['en-GB', 'ja']), 'en');
assert.equal(negotiate(['fr-FR', 'ja-JP']), 'ja');
assert.equal(negotiate([], 'JA-jp'), 'ja');
assert.equal(negotiate(undefined, 'en-US'), 'en');
assert.equal(negotiate(['de-DE'], 'fr-FR'), 'en');
assert.equal(negotiate([null, 1, 'ja']), 'ja');

const html = fs.readFileSync(asset('index.html'), 'utf8');
for (const [, key] of html.matchAll(/data-i18n(?:-(?:aria-label|title|placeholder|alt))?="([^"]+)"/g)) {
  assert.ok(translations.html[key]?.en, key);
  assert.ok(translations.html[key]?.ja, key);
}
for (const group of Object.values(translations)) {
  for (const [key, entry] of Object.entries(group)) {
    assert.deepEqual(Object.keys(entry).sort(), ['en', 'ja'], key);
    assert.doesNotMatch(entry.en, /[\u3040-\u30ff\u3400-\u9fff]/, key);
    const placeholders = text => [...text.matchAll(/\{(\w+)\}/g)].map(m => m[1]).sort();
    assert.deepEqual(placeholders(entry.en), placeholders(entry.ja), key);
  }
}
const catalog = require(shipped ? path.join(shipped, 'catalog.json') : '../examples/catalog.json');
assert.deepEqual(Object.keys(translations.catalog), Object.keys(catalog.proofs));
for (const locale of ['en-US', 'ja-JP']) {
  const i18n = create([locale]);
  const key = Object.keys(catalog.proofs)[0];
  assert.equal(i18n.catalog(key), translations.catalog[key][i18n.locale]);
}

// Static prose is inserted as HTML, without TeX auto-rendering. Keep the
// desktop diagram and proof overview consistent with their English fallback.
for (const key of ['copy-027', 'copy-051', 'copy-181']) {
  const fallback = [...html.matchAll(/data-i18n="([^"]+)"[^>]*>([^<]*)</g)]
    .find(([, candidate]) => candidate === key);
  assert.ok(fallback, key);
  assert.equal(fallback[2], translations.html[key].en, key);
}
for (const locale of ['en', 'ja']) {
  assert.match(translations.html['copy-181'][locale], /√2/);
  assert.doesNotMatch(translations.html['copy-181'][locale], /\\sqrt/);
  // Desktop and mobile diagrams must describe the same LF correspondence.
  const normalize = text => text.replace(/[\s／/]/g, '');
  assert.equal(normalize(translations.html['copy-027'][locale]),
    normalize(translations.html['copy-051'][locale]));
  const key = "Set theory：No universal set via Russell's paradox";
  assert.ok(catalog.proofs[key], 'canonical Russell catalog key');
  assert.equal(create([locale]).catalog(key), translations.catalog[key][locale]);
}

// Exercise locale changes against DOM-like nodes, including static markup,
// accessible labels, and runtime text containing untrusted diagnostic content.
function node(dataset, attributes = {}) {
  return {dataset, attributes, textContent: '', innerHTML: '',
    getAttribute(name) { return attributes[name]; },
    setAttribute(name, value) { attributes[name] = value; }};
}
const heading = node({i18n: 'copy-002'});
const paragraph = node({i18n: 'copy-017'});
const diagram = node({i18n: 'copy-027'});
const overview = node({i18n: 'copy-181'});
const navigation = node({}, {'data-i18n-aria-label': 'attribute-0'});
const status = node({i18n: 'copy-015'});
const root = {
  documentElement: {},
  querySelectorAll(selector) {
    const all = [heading, paragraph, diagram, overview, navigation, status];
    if (selector === '[data-i18n]') return all.filter(n => n.dataset.i18n);
    if (selector === '[data-i18n-message]') return all.filter(n => n.dataset.i18nMessage);
    const attr = selector.slice(1, -1);
    return all.filter(n => n.attributes[attr]);
  }
};
const listeners = new Map();
const context = {
  proofglyphTranslations: translations,
  navigator: {languages: ['ja-JP'], language: 'ja-JP'}, document: root,
  window: {addEventListener(name, fn) { listeners.set(name, fn); },
    dispatchEvent(event) { listeners.get(event.type)?.(event); }},
  Event: class {constructor(type) { this.type = type; }}
};
vm.runInNewContext(fs.readFileSync(asset('i18n.js'), 'utf8'), context);
assert.equal(root.documentElement.lang, 'ja');
assert.equal(diagram.innerHTML, translations.html['copy-027'].ja);
assert.equal(overview.innerHTML, translations.html['copy-181'].ja);
assert.equal(heading.innerHTML, 'エディタ');
assert.match(paragraph.innerHTML, /<code>\.pg<\/code>/);
assert.equal(navigation.attributes['aria-label'], 'ワークスペースとドキュメント');
const i18n = context.proofglyphI18n;
i18n.setText(status, 'checkFailure', {error: '<script>untrusted</script> {count}'});
assert.equal(status.dataset.i18n, undefined);
assert.equal(status.textContent, '検査失敗\n<script>untrusted</script> {count}');
let changeEvents = 0;
listeners.set('proofglyph:languagechange', () => changeEvents++);
context.navigator.languages = ['en-US'];
listeners.get('languagechange')();
assert.equal(root.documentElement.lang, 'en');
assert.equal(diagram.innerHTML, translations.html['copy-027'].en);
assert.equal(overview.innerHTML, translations.html['copy-181'].en);
assert.equal(heading.innerHTML, 'Editor');
assert.equal(navigation.attributes['aria-label'], 'Workspace and documentation');
assert.equal(status.textContent, 'Check failed\n<script>untrusted</script> {count}');
assert.equal(changeEvents, 1);
assert.equal(i18n.t('instructions', {count: i18n.number(1234)}), 'Instructions: 1,234');
context.navigator.languages = ['ja'];
listeners.get('languagechange')();
assert.equal(status.textContent, '検査失敗\n<script>untrusted</script> {count}');
assert.equal(changeEvents, 2);
console.log('Language negotiation, complete dictionaries, catalog labels, DOM updates, and safe runtime text passed.');
