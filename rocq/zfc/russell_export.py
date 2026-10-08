"""Generate one explicit LF proof; both checkers and Rocq verify the output.

This generator is outside the trusted kernel. Formula binders use de Bruijn
indices, and every scope, renaming and context-lifting premise is explicit.
"""
from functools import cache
from pathlib import Path

BOT = ('bottom',)
def mem(x, y): return ('Member', x, y)
def imp(p, q): return ('Implies', p, q)
def all_(p): return ('All', p)
def neg(p): return imp(p, BOT)
def and_(p, q): return neg(imp(p, neg(q)))
def iff(p, q): return and_(imp(p, q), imp(q, p))
def exists(p): return neg(all_(neg(p)))
def app(name, *args): return '(' + ' '.join((name, *args)) + ')'
@cache
def index(n): return 'zero' if n == 0 else app('succ', index(n - 1))
@cache
def formula(p):
    if p == BOT: return 'bottom'
    if p[0] == 'Member': return app('Member', index(p[1]), index(p[2]))
    return app(p[0], *(formula(q) for q in p[1:]))
@cache
def context(g):
    return 'nil' if not g else app('cons', formula(g[0]), context(g[1:]))
@cache
def lt(x, n):
    assert 0 <= x < n
    return app('lt_zero', index(n - 1)) if x == 0 else app('lt_succ', index(x - 1), index(n - 1), lt(x - 1, n - 1))
@cache
def scope(n, p):
    if p == BOT: return app('scoped_bottom', index(n))
    if p[0] == 'Member': return app('scoped_member', index(n), index(p[1]), index(p[2]), lt(p[1], n), lt(p[2], n))
    if p[0] == 'All': return app('scoped_all', index(n), formula(p[1]), scope(n + 1, p[1]))
    return app('scoped_imp', index(n), formula(p[1]), formula(p[2]), scope(n, p[1]), scope(n, p[2]))

# Maps are shift, sep, unbind(x), or up(map).
@cache
def map_term(r):
    if isinstance(r, str): return r + '_map'
    return app(r[0] + '_map', index(r[1]) if r[0] == 'unbind' else map_term(r[1]))
@cache
def maps(r, i):
    if r == 'shift': return i + 1, app('maps_shift', index(i))
    if r == 'sep': return (0, 'maps_sep_zero') if i == 0 else (i + 2, app('maps_sep_succ', index(i - 1)))
    if r[0] == 'unbind':
        x = r[1]
        return (x, app('maps_unbind_zero', index(x))) if i == 0 else (i - 1, app('maps_unbind_succ', index(x), index(i - 1)))
    base = r[1]
    if i == 0: return 0, app('maps_up_zero', map_term(base))
    j, proof = maps(base, i - 1)
    return j + 1, app('maps_up_succ', map_term(base), index(i - 1), index(j), proof)
@cache
def rename(r, p):
    rt = map_term(r)
    if p == BOT: return p, app('rename_bottom', rt)
    if p[0] == 'Member':
        x, a = maps(r, p[1]); y, b = maps(r, p[2])
        return mem(x, y), app('rename_member', rt, index(p[1]), index(p[2]), index(x), index(y), a, b)
    if p[0] == 'All':
        q, proof = rename(('up', r), p[1])
        return all_(q), app('rename_all', rt, formula(p[1]), formula(q), proof)
    u, a = rename(r, p[1]); v, b = rename(r, p[2])
    return imp(u, v), app('rename_imp', rt, formula(p[1]), formula(p[2]), formula(u), formula(v), a, b)
@cache
def lifts(g):
    if not g: return (), 'lifts_nil'
    q, a = rename('shift', g[0]); h, b = lifts(g[1:])
    return (q,) + h, app('lifts_cons', formula(g[0]), formula(q), context(g[1:]), context(h), a, b)

def assume(n, g, p):
    def membership(gs):
        assert gs
        if gs[0] == p: return app('in_here', formula(p), context(gs[1:]))
        return app('in_there', formula(p), formula(gs[0]), context(gs[1:]), membership(gs[1:]))
    return app('nd_assume', index(n), context(g), formula(p), scope(n, p), membership(g))
def intro(n, g, p, q, proof):
    return app('nd_imp_intro', index(n), context(g), formula(p), formula(q), scope(n, p), proof((p,) + g))
def elim(n, g, p, q, a, b):
    return app('nd_imp_elim', index(n), context(g), formula(p), formula(q), a, b)
def specialize(n, g, p, x, proof):
    q, r = rename(('unbind', x), p)
    return app('nd_all_elim', index(n), context(g), formula(p), formula(q), index(x), lt(x, n), r, proof)
def generalize(n, g, p, proof):
    h, r = lifts(g)
    return app('nd_all_intro', index(n), context(g), context(h), formula(p), r, proof(h))
def classical(n, g, p, proof):
    return app('nd_classical', index(n), context(g), formula(p), scope(n, p), proof((neg(p),) + g))
def false_elim(n, g, p, proof):
    return app('nd_false', index(n), context(g), formula(p), scope(n, p), proof)

def and_left(n, g, p, q, proof):
    def contradiction(h):
        def body(k):
            return false_elim(n, k, neg(q), elim(n, k, p, BOT, assume(n, k, neg(p)), assume(n, k, p)))
        return elim(n, h, imp(p, neg(q)), BOT, proof(h), intro(n, h, p, neg(q), body))
    return classical(n, g, p, contradiction)
def and_right(n, g, p, q, proof):
    return classical(n, g, q, lambda h: elim(n, h, imp(p, neg(q)), BOT, proof(h),
        intro(n, h, p, neg(q), lambda k: assume(n, k, neg(q)))))
def and_intro(n, g, p, q, a, b):
    return intro(n, g, imp(p, neg(q)), BOT, lambda h:
        elim(n, h, q, BOT, elim(n, h, p, neg(q), assume(n, h, imp(p, neg(q))), a(h)), b(h)))
def exists_absurd(n, g, p, witness, contradiction):
    return elim(n, g, all_(neg(p)), BOT, witness,
        generalize(n, g, neg(p), lambda h: intro(n + 1, h, p, BOT, contradiction)))

universal = exists(all_(mem(0, 1)))
property_ = all_(iff(mem(0, 1), and_(mem(0, 2), neg(mem(0, 0)))))
predicate = neg(mem(0, 0))
separation = all_(exists(property_))

def separation_proof(g):
    renamed, r = rename('sep', predicate)
    assert renamed == predicate
    ax = app('ax_separation', index(0), formula(predicate), formula(renamed), formula(separation),
        scope(1, predicate), r, app('close_zero', formula(separation)))
    return specialize(1, g, exists(property_), 0,
        app('nd_axiom', index(1), context(g), formula(separation), ax))

def russell_contradiction(g):
    x, u = mem(0, 0), mem(0, 1)
    pair = and_(u, neg(x))
    def biconditional(h):
        return specialize(2, h, property_[1], 0, assume(2, h, property_))
    def forward(h): return and_left(2, h, imp(x, pair), imp(pair, x), biconditional)
    def backward(h): return and_right(2, h, imp(x, pair), imp(pair, x), biconditional)
    def self_negative(h):
        return intro(2, h, x, BOT, lambda k:
            elim(2, k, x, BOT,
                and_right(2, k, u, neg(x), lambda j: elim(2, j, x, pair, forward(j), assume(2, j, x))),
                assume(2, k, x)))
    def in_universal(h): return specialize(2, h, mem(0, 2), 0, assume(2, h, all_(mem(0, 2))))
    return elim(2, g, x, BOT, self_negative(g),
        elim(2, g, pair, x, backward(g), and_intro(2, g, u, neg(x), in_universal, self_negative)))

def proof():
    return intro(0, (), universal, BOT, lambda g:
        exists_absurd(0, g, all_(mem(0, 1)), assume(0, g, universal), lambda h:
            exists_absurd(1, h, property_, separation_proof(h), russell_contradiction)))

if __name__ == '__main__':
    out = Path(__file__).resolve().parent / '_build/russell'
    out.mkdir(parents=True, exist_ok=True)
    (out / 'source.tp').write_text(
        '// Generated by russell_export.py. No additional assumptions.\n'
        'import "../../proof_prelude.tp";\n'
        'theorem proof_no_universal_set : ' + app('Derives', 'zero', 'nil', formula(neg(universal)))
        + '\n  := ' + proof() + ';\n')
