"""Exercise the extracted frontend, including the existing import loader boundary."""
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
CLI = ROOT / "_build" / "rocq4tp"


def run(args, code=0):
    result = subprocess.run([str(CLI), *map(str, args)], capture_output=True, text=True)
    assert result.returncode == code, (args, result.returncode, result.stdout, result.stderr)
    return result


examples = sorted((ROOT.parent / "examples").rglob("*.tp"))
assert examples, "no example sources found"
subprocess.run([str(ROOT / "_build" / "test_frontend"), *map(str, examples)], check=True)
run([], 2)
with tempfile.TemporaryDirectory(prefix="rocq4tp-") as tmp:
    directory = Path(tmp)
    base = directory / "base.tp"
    base.write_text("axiom A : Type;\n")
    left, right, entry = (directory / name for name in ("left.tp", "right.tp", "entry.tp"))
    left.write_text('import "base.tp"; theorem left (x : A) : A := x;\n')
    right.write_text('import "./base.tp"; theorem right (x : A) : A := x;\n')
    entry.write_text('import "left.tp"; import "right.tp";\n')
    assert run(["check", entry]).stdout.strip() == "Accepted 3 declarations"
    encoded = run(["compile", entry]).stdout
    assembly = directory / "entry.pa"
    run(["compile", entry, "-o", assembly])
    assert assembly.read_text() == encoded
    assert run(["check-pa", assembly]).stdout.strip() == "Accepted 3 declarations"
    run(["check-pa", assembly, "--no-axioms"], 1)
    run(["check-pa", assembly, "--fuel", "1"], 1)
    run(["check-pa", assembly, "-o", assembly], 2)
    run(["compile", entry, "-o"], 2)
    run(["compile", entry, "-o", assembly, "-o", assembly], 2)
    run(["compile", entry, "--no-axioms", "-o", assembly], 1)
    assert assembly.read_text() == encoded, "policy rejection overwrote output"
    run(["check", entry, "--no-axioms"], 1)
    run(["check", entry, "--fuel", "1"], 1)
    for fuel in ("0", "-1", "100001", "bad"):
        run(["check", entry, "--fuel", fuel], 2)
    run(["check", entry, "--unknown"], 2)
    run(["check", entry, "--fuel"], 2)
    entry.write_text('import "entry.tp";\n')
    run(["check", entry], 1)
    entry.write_text('import "absent.tp";\n')
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
        run(["check-pa", assembly], 1)
    assembly.write_text(" \t*\n\r: ")
    assert run(["check-pa", assembly]).stdout.strip() == "Accepted 1 declarations"
    entry.write_text("")
    assert run(["check", entry, "--no-axioms"]).stdout.strip() == "Accepted 0 declarations"
    assert run(["compile", entry]).stdout == ""
print("CLI import, pa compilation/decoding, input, policy and resource checks passed")
