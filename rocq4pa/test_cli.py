"""Cross-check the extracted checker against tinyprover, including .tp examples."""
import pathlib
import random
import subprocess
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
CHECKER = ROOT / "rocq4pa/_build/rocq4pa"
ORIGINAL = ROOT / "_build/default/bin/main.exe"


def run(args, expected=0):
    result = subprocess.run(
        [str(x) for x in args], capture_output=True, text=True, timeout=60
    )
    assert result.returncode == expected, (args, result.returncode, result.stdout, result.stderr)
    return result


def main():
    subprocess.run(["dune", "build", "bin/main.exe"], cwd=ROOT, check=True)
    cases = [
        ("", True),
        ("*:", True),
        ("*:#0#0>#0$0\\!", True),
        (" \n*:\t#00#0>#0$00\\!\r", True),
        ("^:", False),
        ("*", False),
        ("@", False),
        ("**:", False),
        ("*!", False),
        ("#0:", False),
        ("$0:", False),
        ("#:", False),
        ("# 0:", False),
        ("#-1:", False),
        ("*x:", False),
        ("*:*:#0:#1#2!", False),
        ("*$0>:", False),
        ("*: #0#0>#0$0\\! #0: #0#1#2@!", True),
        # A proved identity remains opaque: P a is not P (id a).
        ("*:#0#0>#0$0\\!#0:#0*>:#3#2@:#3#1#2@@#4!", False),
        # Eta is absent: P f is not P (fun x => f x).
        ("*:#0#0>:#0#0>*>:#2#1@:#2#0#1$0@\\@#3!", False),
    ]
    with tempfile.TemporaryDirectory(prefix="rocq4pa-test-") as directory:
        tmp = pathlib.Path(directory)
        assembly = tmp / "input.pa"
        for text, accepted in cases:
            assembly.write_text(text)
            expected = 0 if accepted else 1
            run([ORIGINAL, "check", assembly], expected)
            run([CHECKER, "check", assembly], expected)

        # Exhaustion and bounds fail closed; no integer overflow reaches the kernel.
        assembly.write_text("*:#0#0>#0$0\\!")
        run([CHECKER, "check", assembly, "--fuel", "1"], 1)
        run([CHECKER, "check", assembly, "--fuel", "0"], 2)
        run([CHECKER, "check", assembly, "--fuel", "100001"], 2)
        run([CHECKER, "check", assembly, "--no-axioms"], 1)
        for index in ["100001", "9" * 200]:
            assembly.write_text("#" + index + ":")
            run([CHECKER, "check", assembly], 1)

        prelude = tmp / "prelude.pa"
        prelude.write_text("*:")
        assembly.write_text("#0#0>#0$0\\!")
        run([CHECKER, "check", assembly, "--prelude", prelude])
        assembly.write_text("*:")
        run([CHECKER, "check", assembly, "--prelude", prelude], 1)
        prelude.write_text("^:")
        assembly.write_text("")
        run([CHECKER, "check", assembly, "--prelude", prelude], 1)

        # Deterministic mutations exercise the independently implemented parser
        # and checker. Any disagreement is a failure, including unexpected crashes.
        rng = random.Random(420)
        seed = "*:#0#0>#0$0\\!"
        alphabet = "*^$#012>\\@:! \n"
        for _ in range(120):
            chars = list(seed)
            for _ in range(rng.randint(1, 3)):
                pos = rng.randrange(len(chars))
                chars[pos] = rng.choice(alphabet)
            assembly.write_text("".join(chars))
            reference = subprocess.run(
                [str(ORIGINAL), "check", str(assembly)], capture_output=True, timeout=60
            )
            assert reference.returncode in (0, 1)
            run([CHECKER, "check", assembly], reference.returncode)

        sources = sorted((ROOT / "examples").rglob("*.tp"))
        for source in sources:
            run([ORIGINAL, "compile", source, "-o", assembly])
            run([CHECKER, "check", assembly])
        print(f"passed: {len(cases)} fixtures, 120 mutations, resource/prelude checks, {len(sources)} .tp examples")


if __name__ == "__main__":
    main()
