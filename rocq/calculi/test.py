"""Check the fixed pa boundary and malformed evidence with both kernels."""
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'rocq/calculi/_build'
CHECKERS = [ROOT / '_build/default/bin/main.exe', ROOT / 'rocq/pa/_build/rocq4pa']

EXPECTED = '''
Index zero succ Formula Atom Bottom Top Imp Conj Disj Neg Context nil cons
InContext in_here in_there Perm perm_nil perm_cons perm_swap perm_trans
NK nk_assume nk_top nk_bottom nk_imp_intro nk_imp_elim nk_conj_intro
nk_conj_left nk_conj_right nk_disj_left nk_disj_right nk_disj_elim
nk_neg_intro nk_neg_elim nk_classical LK lk_identity lk_bottom lk_top
lk_weak_left lk_weak_right lk_contract_left lk_contract_right
lk_exchange_left lk_exchange_right lk_imp_right lk_imp_left lk_conj_left
lk_conj_right lk_disj_left lk_disj_right lk_neg_left lk_neg_right lk_cut
nk_identity nk_conj_comm nk_excluded_middle lk_imp_identity lk_excluded_middle lk_cut_identity
'''.split()


def run(command, expected=0):
    result = subprocess.run([str(x) for x in command], capture_output=True, text=True, timeout=60)
    assert result.returncode == expected, (command, result.returncode, result.stdout, result.stderr)


def test_separate_preludes(checker, candidate):
    for calculus, auxiliary, count in [
        ('nk', {'InContext', 'in_here', 'in_there', 'NK'}, 32),
        ('lk', {'Perm', 'perm_nil', 'perm_cons', 'perm_swap', 'perm_trans', 'LK'}, 38),
    ]:
        names = (OUT / f'{calculus}-names.txt').read_text().splitlines()
        expected = [name for name in EXPECTED if name in EXPECTED[:14]
                    or name in auxiliary or name.startswith(f'{calculus}_')]
        assert names == expected, (calculus, 'unexpected signature')
        prelude, proofs = OUT / f'{calculus}-prelude.pa', OUT / f'{calculus}-proofs.pa'
        assert prelude.read_text().count(':') == count
        assert proofs.read_text().count('!') == 3 and ':' not in proofs.read_text()
        run([checker, 'check', proofs, '--prelude', prelude])

        def app(name, *args):
            result = '#' + str(names.index(name))
            for arg in args:
                result += arg + '@'
            return result

        nil, bottom = app('nil'), app('Bottom')
        a = app('Atom', app('zero'))
        ga = app('cons', a, nil)
        if calculus == 'nk':
            identity = app('nk_assume', ga, a, app('in_here', a, nil))
            typ, false_typ = app('NK', ga, a), app('NK', nil, bottom)
        else:
            identity = app('lk_identity', a)
            typ, false_typ = app('LK', ga, ga), app('LK', nil, nil)
        candidate.write_text(typ + identity + '!')
        run([checker, 'check', candidate, '--prelude', prelude])
        candidate.write_text(false_typ + identity + '!')
        run([checker, 'check', candidate, '--prelude', prelude], 1)
        candidate.write_text('*:')
        run([checker, 'check', candidate, '--prelude', prelude], 1)


def main():
    names = (OUT / 'names.txt').read_text().splitlines()
    assert names == EXPECTED, 'fixed signature or proof inventory changed'
    prelude, proofs = OUT / 'prelude.pa', OUT / 'proofs.pa'
    assert prelude.read_text().count(':') == 56
    assert proofs.read_text().count('!') == 6 and ':' not in proofs.read_text()
    const = lambda name: '#' + str(names.index(name))

    def app(name, *args):
        result = const(name)
        for arg in args:
            result += arg + '@'
        return result

    def prove(typ, term):
        return typ + term + '!'

    nil, bottom = const('nil'), const('Bottom')
    a = app('Atom', const('zero'))
    b = app('Atom', app('succ', const('zero')))
    ga, gb = app('cons', a, nil), app('cons', b, nil)
    identity = app('lk_identity', a)
    premise = app('nk_assume', ga, a, app('in_here', a, nil))
    invalid = {
        'new assumption': '*:',
        'wrong sort': prove(const('Formula'), '*'),
        'unbound variable': prove(const('Formula'), '$0'),
        'false in empty NK context': prove(app('NK', nil, bottom), premise),
        'wrong hypothesis membership': prove(app('NK', gb, a),
            app('nk_assume', gb, a, app('in_here', b, nil))),
        'drop undischarged hypothesis': prove(app('NK', nil, a), premise),
        'false LK conclusion': prove(app('LK', ga, gb), identity),
        'empty LK succedent': prove(app('LK', ga, nil), identity),
        'NK proof used as LK proof': prove(app('LK', ga, ga), premise),
        'invented exchange': prove(app('Perm', ga, gb),
            app('perm_cons', a, nil, nil, const('perm_nil'))),
        'wrong cut formula': prove(app('LK', ga, ga),
            app('lk_cut', ga, ga, b,
                app('lk_weak_right', ga, ga, a, identity),
                app('lk_weak_left', ga, ga, a, identity))),
        'claim arbitrary atom from identity': prove(app('NK', nil, a),
            app('nk_identity', a)),
    }
    valid = {
        'concrete NK identity': prove(app('NK', nil, app('Imp', a, a)), app('nk_identity', a)),
        'concrete NK excluded middle': prove(app('NK', nil, app('Disj', a, app('Neg', a))),
            app('nk_excluded_middle', a)),
        'concrete LK identity': prove(app('LK', nil, app('cons', app('Imp', a, a), nil)),
            app('lk_imp_identity', a)),
        'concrete LK excluded middle': prove(app('LK', nil,
            app('cons', app('Disj', a, app('Neg', a)), nil)), app('lk_excluded_middle', a)),
    }
    with tempfile.TemporaryDirectory(prefix='calculi-test-') as directory:
        candidate = Path(directory) / 'candidate.pa'
        for checker in CHECKERS:
            test_separate_preludes(checker, candidate)
            run([checker, 'check', proofs, '--prelude', prelude])
            run([checker, 'check', proofs, '--no-axioms'], 1)
            for label, assembly in invalid.items():
                candidate.write_text(assembly)
                try:
                    run([checker, 'check', candidate, '--prelude', prelude], 1)
                except AssertionError as error:
                    raise AssertionError(label) from error
            # Previously proved constants are available only after reading their proofs.
            full_prelude = Path(directory) / 'with-lemmas.pa'
            full_prelude.write_text(prelude.read_text() + proofs.read_text())
            for label, assembly in valid.items():
                candidate.write_text(assembly)
                try:
                    run([checker, 'check', candidate, '--prelude', full_prelude])
                except AssertionError as error:
                    raise AssertionError(label) from error
    print(f'passed: both checkers, 6 generic proofs, {len(valid)} concrete uses, '
          f'{len(invalid)} rejection cases, separate NK/LK preludes and the fixed prelude boundary')


if __name__ == '__main__':
    main()
