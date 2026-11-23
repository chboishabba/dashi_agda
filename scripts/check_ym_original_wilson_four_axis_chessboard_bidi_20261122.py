#!/usr/bin/env python3
"""Original periodic Wilson site-plane/chessboard and R445 BIDI incidence audit.

Exact finite geometry only: literal noncommutative oriented plaquette words
(up to cyclic rotation and inverse), four-axis site reflection, action
halfspaces, selected/spectator native R445 two-link reflection, and the
24 chessboard parity classes. Does NOT certify Haar integration, iterated
reflection-positive chessboard Cauchy-Schwarz, a Wilson polymer measure
estimate, Agda, or a continuum mass gap.
"""
from collections import Counter
from itertools import combinations, product


def shift(x, axis, L):
    y = list(x)
    y[axis] = (y[axis] + 1) % L
    return tuple(y)


def site_reflect(x, axis, b, L):
    y = list(x)
    y[axis] = (2*b-y[axis]) % L
    return tuple(y)


def reflected_bond(edge, axis, b, L):
    x, mu, sign = edge
    if mu == axis:
        return (site_reflect(shift(x,mu,L),axis,b,L),mu,-sign)
    return (site_reflect(x,axis,b,L),mu,sign)


def plaquette(x, mu, nu, L):
    return ((x,mu,1),(shift(x,mu,L),nu,1),
            (shift(x,nu,L),mu,-1),(x,nu,-1))


def inverse_word(w):
    return tuple((x,mu,-sgn) for x,mu,sgn in reversed(w))


def cyclic_trace_class(word):
    return min(seq[j:]+seq[:j] for seq in (word,inverse_word(word))
               for j in range(len(word)))


def halfspace(edge, axis, b, L):
    x,mu = edge
    s = (x[axis]-b) % L
    if mu == axis:
        return 'plus' if s < L//2 else 'minus'
    if s in (0,L//2):
        return 'boundary'
    return 'plus' if s < L//2 else 'minus'


def plaquette_halfspace(word, axis, b, L):
    sides = {halfspace((x,mu),axis,b,L) for x,mu,_ in word}
    assert not {'plus','minus'} <= sides, (axis,b,word,sides)
    return 'plus' if 'plus' in sides else (
        'minus' if 'minus' in sides else 'boundary')


def r445_pairs():
    pairs = {}
    selected = set()
    for c in product(range(2),repeat=4):
        x = tuple(2*j for j in c)
        for mu in range(4):
            a,z = (x,mu),(shift(x,mu,4),mu)
            pairs[(c,mu)] = (a,z)
            selected.update((a,z))
    assert len(pairs)==64 and len(selected)==128
    return pairs,selected


def check_site_plane(L):
    points = list(product(range(L),repeat=4))
    links = {(x,mu) for x in points for mu in range(4)}
    ps = [plaquette(x,mu,nu,L) for x in points
          for mu,nu in combinations(range(4),2)]
    canonical = {cyclic_trace_class(p) for p in ps}
    assert len(links)==4*L**4 and len(canonical)==6*L**4
    if L==4:
        pairs,selected = r445_pairs()
        pair_by_set = {frozenset(p):p for p in pairs.values()}
        assert len(links-selected)==896
    for axis in range(4):
        for b in (0,1):
            link_counts = Counter(halfspace(e,axis,b,L) for e in links)
            assert link_counts == Counter({
                'plus':(4*L**4-6*L**3)//2,
                'minus':(4*L**4-6*L**3)//2,
                'boundary':6*L**3})
            p_counts = Counter(plaquette_halfspace(p,axis,b,L) for p in ps)
            assert p_counts == Counter({
                'plus':(6*L**4-6*L**3)//2,
                'minus':(6*L**4-6*L**3)//2,
                'boundary':6*L**3})
            transformed = {}
            for x,mu in links:
                e = reflected_bond((x,mu,1),axis,b,L)
                assert reflected_bond(e,axis,b,L)==(x,mu,1)
                transformed[(x,mu)]=(e[0],e[1])
                old = halfspace((x,mu),axis,b,L)
                new = halfspace((e[0],e[1]),axis,b,L)
                assert (old,new) in (
                    ('plus','minus'),('minus','plus'),
                    ('boundary','boundary'))
            assert len(set(transformed.values()))==len(links)
            for w in ps:
                reflected=tuple(reflected_bond(e,axis,b,L) for e in w)
                assert cyclic_trace_class(reflected) in canonical
                old=plaquette_halfspace(w,axis,b,L)
                new=plaquette_halfspace(reflected,axis,b,L)
                assert (old,new) in (
                    ('plus','minus'),('minus','plus'),
                    ('boundary','boundary'))
            if L==4:
                assert {transformed[e] for e in selected}==selected
                assert {transformed[e] for e in links-selected}==links-selected
                for pair in pairs.values():
                    edges=tuple(reflected_bond((x,mu,1),axis,b,L)
                                for x,mu in pair)
                    p=pair_by_set[frozenset((x,mu) for x,mu,_ in edges)]
                    if axis==pair[0][1]:
                        assert edges==tuple((x,mu,-1) for x,mu in reversed(p))
                    else:
                        assert edges==tuple((x,mu,1) for x,mu in p)
    print('PASS original Wilson L=%d links=%d plaquettes=%d site-planes=8'
          % (L,len(links),len(ps)))


def check_chessboard(L):
    bad_original=0
    marks=0
    for mu,nu in combinations(range(4),2):
        transverse=[j for j in range(4) if j not in (mu,nu)]
        for shifts in product((0,1),repeat=2):
            seen=Counter()
            for x in product(range(L),repeat=4):
                y=list(x)
                for j,s in zip(transverse,shifts):
                    old=(x[j]+x[j]%2+s)%L
                    correct=(x[j]+((s-x[j])%2))%L
                    faces={x[j],(x[j]+1)%L}
                    bad_original+=old not in faces
                    assert correct in faces
                    y[j]=correct
                seen[tuple(y)]+=1
                marks+=1
            assert len(seen)==L**4//4 and set(seen.values())=={4}
    assert bad_original>0
    print('PASS chessboard L=%d tile_marks=%d old_off_cube=%d corrected_off_cube=0'
          % (L,marks,bad_original))


def main():
    for L in (4,6):
        check_site_plane(L)
    for L in (4,6,8):
        check_chessboard(L)
    print('SCOPE: finite geometry/word trace only; native chessboard RP and W3 still open')


if __name__=='__main__':
    main()
