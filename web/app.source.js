"use strict";
const example = document.getElementById("example");
let sourcemap = null;
let sourcePath = "examples/browser.tp";
const tp = document.getElementById("tp");
const pa = document.getElementById("pa");
const result = document.getElementById("result");
const status = document.getElementById("status");
const compileButton = document.getElementById("compile");
const checkButton = document.getElementById("check");

function check() {
  const checked = (sourcemap ? globalThis.tinyprover.checkMapped : globalThis.tinyprover.check)(pa.value);
  const proofs = checked.ok ? checked.output.split("\n").flatMap(line => {
    const match = /^(\S+) \[proven\]/.exec(line);
    return match ? [`${match[1]}: 検査成功`] : [];
  }) : [];
  result.value = checked.ok ? (proofs.join("\n") || "検査成功") : `検査失敗\n${checked.output}`;
  status.textContent = checked.ok ? "検査成功" : "検査失敗";
}

function compile() {
  sourcemap = null;
  const compiled = globalThis.tinyprover.compileAt(sourcePath, tp.value);
  if (!compiled.ok) {
    pa.value = "";
    result.value = compiled.output;
    status.textContent = "コンパイル失敗";
    return;
  }
  pa.value = compiled.output;
  sourcemap = JSON.parse(compiled.sourcemap);
  check();
}

tp.addEventListener("input", () => {
  sourcemap = null;
  result.value = "";
  status.textContent = "tp が変更されました。再コンパイルしてください。";
});
pa.addEventListener("input", () => {
  sourcemap = null;
  result.value = "";
  status.textContent = "pa が変更されました。再検査してください。";
});
async function initialize() {
if (globalThis.tinyprover) {
  const sources = new Map(JSON.parse(globalThis.tinyprover.examples)
    .map(entry => [entry.path, entry.source]));
  compileButton.disabled = false;
  checkButton.disabled = false;
  compileButton.addEventListener("click", compile);
  checkButton.addEventListener("click", check);
  compile();
  let catalog;
  try {
    const response = await fetch("catalog.json");
    if (!response.ok) throw new Error(`HTTP ${response.status}`);
    catalog = await response.json();
  } catch (error) {
    status.textContent = `カタログの読み込みに失敗しました: ${error.message}`;
    return;
  }
  function addGroup(label, prefix, items) {
    const group = document.createElement("optgroup");
    group.label = label;
    for (const [name, key] of items) {
      const option = document.createElement("option");
      option.value = JSON.stringify([prefix, ...key]);
      option.textContent = name;
      group.append(option);
    }
    example.append(group);
  }
  addGroup("証明例", "proof", Object.entries(catalog.proofs).flatMap(([name, matches]) => {
    const paths = [...new Set(matches.map(match => match.path))];
    return paths.map(path => {
      const index = matches.findIndex(match => match.path === path);
      const label = paths.length === 1 ? name : `${name}（${matches[index].name}）`;
      return [label, [name, index]];
    });
  }));
  example.disabled = false;
  example.addEventListener("change", () => {
    if (!example.value) return;
    const [, name, index] = JSON.parse(example.value);
    const path = catalog.proofs[name][index].path;
    const source = sources.get(path);
    if (source === undefined) {
      status.textContent = `ソースが見つかりません: ${path}`;
      return;
    }
    result.value = "";
    if (path.endsWith(".pa")) {
      sourcemap = null;
      tp.value = "";
      sourcePath = "examples/browser.tp";
      pa.value = source;
      check();
    } else {
      sourcePath = path;
      tp.value = source;
      compile();
    }
  });

} else {
  status.textContent = "読み込みに失敗しました。";
}

}
initialize();
