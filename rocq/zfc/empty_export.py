"""Generate the empty-set certificate from Infinity, without a new axiom.

Like russell_export.py, this generator is checked by Rocq and both checkers.
"""
from pathlib import Path
from russell_export import (
    BOT, mem, imp, all_, neg, and_, iff, exists, app, index, formula, context,
    assume, intro, elim, specialize, classical, and_left, and_right, exists_absurd,
)

empty_property = all_(neg(mem(0, 1)))
empty_set = exists(empty_property)
empty_member = and_(mem(0, 1), empty_property)
successor = all_(imp(mem(0, 1), exists(and_(mem(0, 2),
    all_(iff(mem(0, 1), imp(neg(mem(0, 2)), ('Equal', 0, 2))))))))
infinity_body = and_(exists(empty_member), successor)
infinity = exists(infinity_body)


def proof():
    def inner(g):
        def empty_witness(h):
            def contradiction(k):
                return elim(2, k, empty_property, BOT,
                    specialize(2, k, neg(empty_property), 0,
                               assume(2, k, all_(neg(empty_property)))),
                    and_right(2, k, mem(0, 1), empty_property,
                              lambda j: assume(2, j, empty_member)))
            return elim(2, h, empty_set, BOT, assume(2, h, neg(empty_set)),
                        intro(2, h, all_(neg(empty_property)), BOT, contradiction))
        return exists_absurd(1, g, empty_member,
            and_left(1, g, exists(empty_member), successor,
                     lambda h: assume(1, h, infinity_body)), empty_witness)
    return classical(0, (), empty_set, lambda g:
        exists_absurd(0, g, infinity_body,
            app('nd_axiom', index(0), context(g), formula(infinity), 'ax_infinity'), inner))


if __name__ == '__main__':
    root = Path(__file__).resolve().parent
    source = (root / 'proof_certificates.ht').read_text()
    certificate = ('theorem proof_empty : ' + app('Derives', 'zero', 'nil', formula(empty_set))
                   + '\n  := ' + proof() + ';')
    source = source.replace('"proof_prelude.ht"', '"../../proof_prelude.ht"')
    assert source.count('// EMPTY_SET_DERIVATION') == 1
    (root / '_build/deep/source.ht').write_text(source.replace('// EMPTY_SET_DERIVATION', certificate))
