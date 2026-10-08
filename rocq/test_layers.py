"""Keep language theory independent of algorithms and correspondence proofs."""
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parent
LANGUAGE = {
    "Pa": set("Syntax Substitution Program WellFormed TypingSubstitution EvaluationSpec Confluence Generation Preservation Regularity Normalization Arity Reducibility TypedNormalization CheckerSpec CodecSpec".split()),
    "Tp": set("Surface DesugarSpec ResolveSpec CompileSpec TpSyntaxSpec TpImportsSpec FileSpec".split()),
}
IMPORT = re.compile(r"From\s+Tinyprover\.(Pa|Tp)\s+Require\s+(?:Import|Export)\s+([^.]*)\.", re.S)
modules = {(ns, p.stem): p for ns, directory in (("Pa", "pa"), ("Tp", "tp"))
           for p in (ROOT / directory).glob("*.v")}


for directory in ("pa", "tp"):
    development = ROOT / directory
    files = subprocess.check_output(
        ["make", "--no-print-directory", "-s", "-C", str(development), "print-vfiles"],
        text=True,
    ).split()
    project = [line for line in (development / "_CoqProject").read_text().splitlines() if line.endswith(".v")]
    assert files == project, f"{directory}: Makefile and _CoqProject module orders differ"
    assert len(files) == len(set(files)), f"{directory}: duplicate module in build order"
    assert set(files) == {p.name for p in development.glob("*.v")}, (
        f"{directory}: _CoqProject must list every proof module exactly once"
    )


def layer(ns, name):
    if name in LANGUAGE[ns]:
        return "language"
    if name.endswith("Impl"):
        return "implementation"
    return "correspondence"


for (ns, name), path in modules.items():
    source = re.sub(r"\(\*.*?\*\)", "", path.read_text(), flags=re.S)
    own = layer(ns, name)
    if own == "correspondence":
        continue
    for dependency_ns, names in IMPORT.findall(source):
        for dependency in names.split():
            assert (dependency_ns, dependency) in modules, (path, dependency)
            target = layer(dependency_ns, dependency)
            assert target == "language" or (own == "implementation" and target == "implementation"), (
                f"{ns}.{name} ({own}) depends on {dependency_ns}.{dependency} ({target})"
            )
print("Language and implementation dependency boundaries passed")
