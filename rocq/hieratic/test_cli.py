"""Exercise the extracted frontend, including extracted parsing and import graph expansion."""
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
CLI = ROOT / "_build" / "hieratic"


def run(args, code=0):
    result = subprocess.run([str(CLI), *map(str, args)], capture_output=True, text=True)
    assert result.returncode == code, (args, result.returncode, result.stdout, result.stderr)
    return result


examples = sorted((ROOT.parent.parent / "examples").rglob("*.ht"))
assert examples, "no example sources found"
subprocess.run([str(ROOT / "_build" / "test_frontend"), *map(str, examples)], check=True)
for example in examples:
    run(["check", example])
run([], 2)
with tempfile.TemporaryDirectory(prefix="hieratic-") as tmp:
    directory = Path(tmp)
    base = directory / "base.ht"
    base.write_text("axiom A : Type;\n")
    left, right, entry = (directory / name for name in ("left.ht", "right.ht", "entry.ht"))
    left.write_text('import "base.ht"; theorem left (x : A) : A := x;\n')
    right.write_text('import "./base.ht"; theorem right (x : A) : A := x;\n')
    entry.write_text('import "left.ht"; import "right.ht";\n')
    assert run(["check", entry]).stdout.strip() == "Accepted 3 declarations"
    # Canonical identity includes symlinks; imports use the real file's directory.
    alias = directory / "alias.ht"
    alias.symlink_to(base)
    right.write_text('import "alias.ht"; theorem right (x : A) : A := x;\n')
    assert run(["check", entry]).stdout.strip() == "Accepted 3 declarations"
    nested = directory / "nested"
    nested.mkdir()
    (nested / "base.ht").write_text("axiom B : Type;\n")
    (nested / "module.ht").write_text('import "base.ht";\n')
    (directory / "module-link.ht").symlink_to(nested / "module.ht")
    assert run(["check", directory / "module-link.ht"]).stdout.strip() == "Accepted 1 declarations"
    assert run(["compile", directory / "module-link.ht"]).stdout == "*:"
    encoded = run(["compile", entry]).stdout
    assembly = directory / "entry.pg"
    run(["compile", entry, "-o", assembly])
    assert assembly.read_text() == encoded
    assert run(["check-proofglyph", assembly]).stdout.strip() == "Accepted 3 declarations"
    run(["check-proofglyph", assembly, "--no-axioms"], 1)
    run(["check-proofglyph", assembly, "--fuel", "1"], 1)
    run(["check-proofglyph", assembly, "-o", assembly], 2)
    run(["compile", entry, "-o"], 2)
    run(["compile", entry, "-o", assembly, "-o", assembly], 2)
    run(["compile", entry, "--no-axioms", "-o", assembly], 1)
    assert assembly.read_text() == encoded, "policy rejection overwrote output"
    run(["check", entry, "--no-axioms"], 1)
    assert run(["check", entry, "--fuel", "100000"]).stdout.strip() == "Accepted 3 declarations"
    run(["check", entry, "--fuel", "1"], 1)
    for fuel in ("0", "-1", "100001", "bad"):
        run(["check", entry, "--fuel", fuel], 2)
    run(["check", entry, "--unknown"], 2)
    run(["check", entry, "--fuel"], 2)
    entry.write_text('import "entry.ht";\n')
    run(["check", entry], 1)
    entry.write_text('import "absent.ht";\n')
    run(["check", entry], 1)
    # Rejection must preserve previously compiled output for frontend failures.
    for source in ('import "entry.ht";', 'import "absent.ht";',
                   'import "";', 'axiom A : Type?;', 'def f : Type;'):
        entry.write_text(source)
        run(["compile", entry, "-o", assembly], 1)
        assert assembly.read_text() == encoded, "frontend rejection overwrote output"
    malformed = directory / "malformed.ht"
    malformed.write_text("axiom A : ;")
    entry.write_text('import "malformed.ht";')
    assert str(malformed.resolve()) in run(["check", entry], 1).stderr
    entry.write_text('theorem early (x : A) : A := x; import "base.ht";')
    run(["check", entry], 1)
    entry.write_text('import "base.ht"; axiom A : Type;')
    run(["check", entry], 1)
    entry.write_text("axiom missing : ;\n")
    run(["check", entry], 1)
    entry.write_text("axiom A : A;\n")
    run(["check", entry], 1)
    entry.write_text("axiom bad : Kind;\n")
    run(["check", entry], 1)
    run(["compile", entry, "-o", assembly], 1)
    assert assembly.read_text() == encoded, "typing rejection overwrote output"
    for source in ("#:" , "*:*", "**:", "***!", "^:", "*:?", "# 0:"):
        assembly.write_text(source)
        run(["check-proofglyph", assembly], 1)
    assembly.write_text(" \t*\n\r: ")
    assert run(["check-proofglyph", assembly]).stdout.strip() == "Accepted 1 declarations"
    # Transparent definitions affect later types; theorem bodies stay opaque.
    entry.write_text("symbol A : Type; symbol a : A; def T : Type := A; "
                     "def id (x : T) : T := x; theorem good : T := id a;")
    assert run(["check", entry]).stdout.strip() == "Accepted 5 declarations"
    transparent = run(["compile", entry]).stdout
    assert run(["compile", entry, "--elaborate"]).stdout == transparent
    run(["check", entry, "--no-axioms"], 1)
    entry.write_text("symbol A : Type; symbol a : A; theorem T : Type := A; "
                     "theorem bad : T := a;")
    run(["check", entry], 1)
    # The unreduced pass must reject ill-typed arguments erased by beta reduction.
    for argument in ("Type", "Kind"):
        entry.write_text("symbol A : Type; symbol a : A; "
                         "def ignore (x : A) : A := a; "
                         f"theorem bad : A := ignore {argument};")
        run(["check", entry], 1)
    # Closed macro bodies must not capture a new local binder.
    entry.write_text("symbol A : Type; def id (x : A) : A := x; "
                     "theorem nested (x : A) (y : A) : A := id x;")
    assert run(["check", entry]).stdout.strip() == "Accepted 3 declarations"
    for source in ("def self : Type := self;", "def early : Type := later; symbol later : Type;",
                   "symbol A : Type; def A : Type := A;"):
        entry.write_text(source)
        run(["check", entry], 1)
    entry.write_text("")
    assert run(["check", entry, "--no-axioms"]).stdout.strip() == "Accepted 0 declarations"
    assert run(["compile", entry]).stdout == ""
print("CLI import, proofglyph compilation/decoding, input, policy and resource checks passed")
