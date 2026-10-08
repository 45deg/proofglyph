"""Exercise the exported prelude/proof boundary with both independent checkers."""
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / 'zfc/_build'
CHECKERS = [ROOT / '_build/default/bin/main.exe', ROOT / 'rocq4pa/_build/rocq4pa']


def run(command, expected=0):
    result = subprocess.run([str(x) for x in command], capture_output=True, text=True, timeout=60)
    assert result.returncode == expected, (command, result.returncode, result.stdout, result.stderr)
    return result


def main():
    names = (OUT / 'names.txt').read_text().splitlines()
    assert names[-5:] == [
        'set_eq_sym', 'empty_unique', 'empty_unique_quantified',
        'inhabited_not_empty', 'pair_order_irrelevant',
    ]
    allowed = {
        'Prop', 'Prf', 'And', 'and_intro', 'and_left', 'and_right', 'Or', 'or_elim',
        'Not', 'False', 'not_intro', 'not_elim', 'or_left', 'or_right', 'false_elim',
        'U', 'Exists', 'exists_intro', 'All', 'all_elim', 'all_intro', 'exists_elim',
        'Eq', 'eq_refl', 'eq_subst', 'excluded_middle',
        'Mem', 'set_ext', 'empty_exists', 'pair_exists',
    }
    assert len(names[:-5]) == len(allowed) and set(names[:-5]) == allowed
    prelude = OUT / 'prelude.pa'
    proofs = OUT / 'proofs.pa'
    assert ':' not in proofs.read_text()
    with tempfile.TemporaryDirectory(prefix='zfc-test-') as directory:
        bad = Path(directory) / 'bad.pa'
        for checker in CHECKERS:
            run([checker, 'check', proofs, '--prelude', prelude])
            # Same terms are not accepted without their fixed prelude.
            run([checker, 'check', proofs, '--no-axioms'], 1)
            # A fresh axiom in the proof file is always rejected.
            bad.write_text(proofs.read_text() + '*:')
            run([checker, 'check', bad, '--prelude', prelude], 1)
            # Type is not an inhabitant of the set domain U (constant 15).
            u = names.index('U')
            bad.write_text(f'#{u}*!')
            run([checker, 'check', bad, '--prelude', prelude], 1)
    test_deep()
    test_russell()
    print('passed: legacy and full-theory preludes, Russell proof, both checkers, schema guards and binder renaming')


def test_russell():
    out = OUT / 'russell'
    prelude, proofs = out / 'prelude.pa', out / 'proofs.pa'
    assert prelude.read_bytes() == (OUT / 'deep/prelude.pa').read_bytes()
    assert (out / 'names.txt').read_text().splitlines() == (
        (OUT / 'deep/names.txt').read_text().splitlines()[:83]
        + ['proof_no_universal_set'])
    assembly = proofs.read_text()
    assert ':' not in assembly and assembly.count('!') == 1
    for checker in CHECKERS:
        run([checker, 'check', proofs, '--prelude', prelude])
        run([checker, 'check', proofs, '--no-axioms'], 1)


def test_deep():
    out = OUT / 'deep'
    names = (out / 'names.txt').read_text().splitlines()
    # Fixed declaration inventory: no extra assumptions may enter unnoticed.
    expected = """
      Index zero succ Formula bottom Equal Member Implies All
      Lt lt_zero lt_succ Scoped scoped_bottom scoped_equal scoped_member scoped_imp scoped_all
      Map shift_map unbind_map up_map sep_map value_map unique_map image_map Maps
      maps_shift maps_unbind_zero maps_unbind_succ maps_up_zero maps_up_succ
      maps_sep_zero maps_sep_succ maps_value_zero maps_value_one maps_value_tail
      maps_unique_zero maps_unique_one maps_unique_tail maps_image_zero maps_image_one maps_image_tail
      Renames rename_bottom rename_equal rename_member rename_imp rename_all
      Closes close_zero close_succ Context nil cons InContext in_here in_there
      Lifts lifts_nil lifts_cons Zax ax_extensionality ax_empty ax_pairing ax_union ax_power
      ax_infinity ax_foundation ax_choice ax_separation ax_replacement Derives
      nd_assume nd_axiom nd_imp_intro nd_imp_elim nd_false nd_classical nd_all_intro
      nd_all_elim nd_eq_refl nd_eq_subst
    """.split()
    proved = ['proof_' + x for x in [
        'extensionality', 'empty', 'pairing', 'union', 'power', 'infinity', 'foundation',
        'choice', 'eq_reflexive', 'identity', 'separation', 'replacement', 'renaming_binder',
    ]]
    assert names == expected + proved
    prelude, proofs = out / 'prelude.pa', out / 'proofs.pa'
    assert ':' not in proofs.read_text()
    # Malformed evidence is tested at assembly level with both checkers.
    const = lambda name: '#' + str(names.index(name))
    app = lambda f, x: f + x + '@'
    scope_bad = app(app(const('Scoped'), const('zero')),
                    app(app(const('Member'), const('zero')), const('zero')))
    scope_wrong = app(app(app(const('scoped_member'), const('zero')), const('zero')), const('zero'))
    scope_wrong = app(app(scope_wrong, app(const('lt_zero'), const('zero'))),
                      app(const('lt_zero'), const('zero')))
    up_map = app(const('up_map'), const('sep_map'))
    rename_bad = app(app(app(const('Renames'), up_map), const('bottom')), const('bottom'))
    rename_wrong = app(const('rename_bottom'), const('sep_map'))
    def apps(name, *args):
        term = const(name)
        for arg in args:
            term = app(term, arg)
        return term
    # A beta-expanded proof exercises acceptance beyond constructor trees.
    z = const('zero')
    one = apps('succ', z)
    eq = apps('Equal', z, z)
    target = apps('Derives', z, const('nil'), apps('All', eq))
    refl = apps('nd_eq_refl', one, const('nil'), z, apps('lt_zero', z))
    closed_refl = apps('nd_all_intro', z, const('nil'), const('nil'), eq, const('lifts_nil'), refl)
    beta_proof = app(target + '$0' + '\\', closed_refl)
    with tempfile.TemporaryDirectory(prefix='zfc-deep-test-') as directory:
        bad = Path(directory) / 'bad.pa'
        expanded = Path(directory) / 'beta.pa'
        expanded.write_text(target + beta_proof + '!')
        for checker in CHECKERS:
            run([checker, 'check', expanded, '--prelude', prelude])
            run([checker, 'check', proofs, '--prelude', prelude])
            run([checker, 'check', proofs, '--no-axioms'], 1)
            for malformed in [
                '*:',                         # new assumption
                scope_bad + scope_wrong + '!', # free variables claimed closed
                rename_bad + rename_wrong + '!', # map not lifted under a binder
            ]:
                bad.write_text(malformed)
                run([checker, 'check', bad, '--prelude', prelude], 1)
    # Check the schema guard itself, rather than just a standalone Scoped family.
    with tempfile.TemporaryDirectory(prefix='zfc-schema-test-') as directory:
        bad = Path(directory) / 'bad.tp'
        prelude_source = (ROOT / 'zfc/proof_prelude.tp').as_posix()
        sep = next(line for line in Path(prelude_source).read_text().splitlines()
                   if line.strip().startswith('-> Closes n '))
        sep_body = sep.split('-> Closes n ', 1)[1].rsplit(' result -> Zax result;', 1)[0]
        bad.write_text(f'import "{prelude_source}";\n' + """
          theorem bad_guard : forall (renamed result : Formula),
            Renames sep_map (Member zero (succ zero)) renamed
            -> Closes zero SEP_BODY result -> Zax result
            := fun (renamed result : Formula)
              (r : Renames sep_map (Member zero (succ zero)) renamed)
              (c : Closes zero SEP_BODY result) =>
                ax_separation zero (Member zero (succ zero)) renamed result
                  (scoped_member (succ zero) zero (succ zero)
                    (lt_zero zero) (lt_succ zero (succ zero) (lt_zero zero))) r c;
        """.replace("SEP_BODY", sep_body))
        rejected = run([CHECKERS[0], 'compile', bad], 1)
        assert "type mismatch" in rejected.stderr.lower(), rejected.stderr


if __name__ == '__main__':
    main()
