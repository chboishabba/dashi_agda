#!/usr/bin/env python3
"""Exact finite checks for P0 guarded-implication obstruction geometry.
No third-party dependencies. Not an asymptotic lower bound or kernel certificate.
"""
from itertools import combinations
from random import Random


def antichain(family):
    out = []
    for s in sorted(set(family), key=lambda x: (len(x), tuple(sorted(x)))):
        if not any(t.issubset(s) for t in out):
            out.append(s)
    return tuple(out)


def join(a, b):
    d = dict(a)
    for i, v in b:
        if i in d and d[i] != v:
            return None
        d[i] = v
    return frozenset(d.items())


def plus(a, b):
    return antichain((*a, *b))


def times(a, b):
    return antichain(u for x in a for y in b if (u := join(x, y)) is not None)


def obstructions(q, r, clauses):
    n = 2 * r
    A = [[tuple() for _ in range(n)] for _ in range(n)]
    for i in range(n):
        A[i][i] = (frozenset(),)
    for C in clauses:
        L = [(i, 1-v) for i, v in C if i < q]
        R = [(i-q, v) for i, v in C if i >= q]
        assert L and 1 <= len(R) <= 2 and len(C) <= 3
        g = frozenset(L)
        a, b = 2*R[0][0]+R[0][1], 2*R[-1][0]+R[-1][1]
        A[a^1][b] = plus(A[a^1][b], (g,))
        A[b^1][a] = plus(A[b^1][a], (g,))
    for k in range(n):
        P = A
        N = [[P[i][j] for j in range(n)] for i in range(n)]
        for i in range(n):
            for j in range(n):
                if P[i][k] and P[k][j]:
                    N[i][j] = plus(N[i][j], times(P[i][k], P[k][j]))
        A = N
    out = []
    for i in range(r):
        out.extend(times(A[2*i][2*i+1], A[2*i+1][2*i]))
    return antichain(out)


def sat2(q, r, clauses, x):
    n = 2*r
    reach = [1 << i for i in range(n)]
    for C in clauses:
        if any(((x >> i) & 1) == v for i, v in C if i < q):
            continue
        R = [(i-q, v) for i, v in C if i >= q]
        assert 1 <= len(R) <= 2
        a, b = 2*R[0][0]+R[0][1], 2*R[-1][0]+R[-1][1]
        reach[a^1] |= 1 << b
        reach[b^1] |= 1 << a
    for k in range(n):
        bit, row = 1 << k, reach[k]
        for i in range(n):
            if reach[i] & bit:
                reach[i] |= row
    return not any((reach[2*i] >> (2*i+1) & 1) and
                   (reach[2*i+1] >> (2*i) & 1) for i in range(r))


def contains(pins, x):
    return all((x >> i & 1) == v for i, v in pins)


def signed_ie(q, O, eta):
    total = 0
    for mask in range(1 << len(O)):
        tau, ok = frozenset(), True
        for j, sigma in enumerate(O):
            if mask >> j & 1:
                tau = join(tau, sigma)
                if tau is None:
                    ok = False
                    break
        if not ok:
            continue
        fixed = dict(tau)
        if any((eta >> i & 1) and i not in fixed for i in range(q)):
            inner = 0
        else:
            phase = sum((eta >> i & 1)*v for i, v in fixed.items()) & 1
            inner = (-1 if phase else 1) * (1 << (q-len(fixed)))
        total += (-1 if mask.bit_count() & 1 else 1) * inner
    return total


def brute_signed(q, O, eta):
    return sum((-1 if (eta & x).bit_count() & 1 else 1)
               for x in range(1 << q)
               if not any(contains(s, x) for s in O))


def parity_formula(q):
    # L=(g,x_0,...,x_(q-1)); R=(z_0,...,z_q).
    Q, r, C = q+1, q+1, []
    for i in range(q):
        x, a, b = 1+i, Q+i, Q+i+1
        C.extend([
            ((x,1),(a,1),(b,0)), ((x,0),(a,0),(b,0)),
            ((x,0),(a,1),(b,1)), ((x,1),(a,0),(b,1)),
        ])
    C.extend([((0,1),(Q,0)), ((0,1),(Q+q,0))])
    return Q, r, C


def random_cover_tests():
    rng, assignments, terms, max_terms = Random(369), 0, 0, 0
    for _ in range(300):
        q, r = rng.randint(1,4), rng.randint(1,4)
        C = []
        for _ in range(rng.randint(0, min(18,4*(q+r)))):
            w = rng.randint(2,min(3,q+r))
            while True:
                vs = rng.sample(range(q+r),w)
                if any(v<q for v in vs) and any(v>=q for v in vs): break
            C.append(tuple((v,rng.randrange(2)) for v in vs))
        O = obstructions(q,r,C)
        max_terms, terms = max(max_terms,len(O)), terms+len(O)
        for x in range(1<<q):
            assert sat2(q,r,C,x) == (not any(contains(s,x) for s in O))
            assignments += 1
    return 300, assignments, terms, max_terms


def random_signed_tests():
    rng, modes, max_terms = Random(1701), 0, 0
    for _ in range(250):
        q, r = rng.randint(1,4), rng.randint(1,4)
        C = []
        for _ in range(rng.randint(0,min(16,3*(q+r)))):
            w = rng.randint(2,min(3,q+r))
            while True:
                vs = rng.sample(range(q+r),w)
                if any(v<q for v in vs) and any(v>=q for v in vs): break
            C.append(tuple((v,rng.randrange(2)) for v in vs))
        O = obstructions(q,r,C)
        max_terms = max(max_terms,len(O))
        for eta in range(1<<q):
            assert signed_ie(q,O,eta) == brute_signed(q,O,eta)
            modes += 1
    return 250, modes, max_terms


def parity_tests():
    rows = []
    for q in range(1,7):
        Q,r,C = parity_formula(q)
        O = obstructions(Q,r,C)
        assert len(O) == 1 << (q-1)
        for s in O:
            d = dict(s)
            assert d[0] == 0 and len(d) == q+1
            assert sum(d[i+1] for i in range(q)) & 1
        rows.append((q,len(C),len(O)))
    signed_modes, zeros = 0, []
    for q in range(1,5):
        Q,r,C = parity_formula(q)
        O = obstructions(Q,r,C)
        z = signed_ie(Q,O,0)
        assert z == 3*(1 << (q-1))
        zeros.append((q,z))
        for eta in range(1<<Q):
            assert signed_ie(Q,O,eta) == brute_signed(Q,O,eta)
            signed_modes += 1
    return rows, zeros, signed_modes


DIGITS = "737362511425175275471342317614566635167417725234"


def zero_gadget():
    out = []
    scopes = (I for I in combinations(range(8),3) if min(I)<4<=max(I))
    for I,d in zip(scopes,DIGITS):
        p = int(d)
        out.append(tuple((i,1-(p>>j&1)) for j,i in enumerate(I)))
    return out


def side_copy_compile(qL,qR,source):
    off, nxt = qL+qR, qL+qR+8
    L, R = set(range(qL))|set(range(off,off+4)), set(range(qL,off))|set(range(off+4,off+8))
    C = [tuple((off+i,b) for i,b in c) for c in zero_gadget()]
    for clause in source:
        copies = []
        for v,b in clause:
            cp, isL = nxt, v in L
            nxt += 1
            (L if isL else R).add(cp)
            copies.append((cp,b))
            za,zb = ((off+6,off+7) if isL else (off,off+1))
            C.extend([((v,0),(cp,1),(za,1)),((v,1),(cp,0),(zb,1))])
        if len(copies)==2: copies.append((off+4,1))
        if len(copies)==1: copies.extend([(off+4,1),(off+5,1)])
        assert len(copies)==3
        C.append(tuple(copies))
    scopes = [tuple(sorted(v for v,_ in c)) for c in C]
    assert len(scopes)==len(set(scopes))
    assert all(len(c)==3 and len({v for v,_ in c})==3 for c in C)
    assert all(any(v in L for v,_ in c) and any(v in R for v,_ in c) for c in C)
    return nxt,L,R,C


def local_full_parity_smoke():
    q,r,source = parity_formula(1)
    n,L,R,C = side_copy_compile(q,r,source)
    assert [x for x in range(256) if all(any((x>>v&1)==b for v,b in c)
                                         for c in zero_gadget())] == [0]
    lvars,rvars = sorted(L),sorted(R)
    ren = {v:i for i,v in enumerate(lvars)}
    ren.update({v:len(lvars)+i for i,v in enumerate(rvars)})
    CC = [tuple((ren[v],b) for v,b in c) for c in C]
    good, counts = [], []
    for x in range(1<<len(lvars)):
        if sat2(len(lvars),len(rvars),CC,x):
            good.append(x)
            count = 0
            for y in range(1<<len(rvars)):
                count += all(any(
                    (((x >> v) & 1) if v < len(lvars) else
                     ((y >> (v-len(lvars))) & 1)) == b
                    for v,b in c) for c in CC)
            counts.append(count)
    assert (len(lvars),len(rvars),len(C),len(good),sorted(counts),sum(counts)) == (12,16,86,3,[1,2,2],5)
    return len(lvars),len(rvars),len(C),len(good),sorted(counts)


def main():
    print("random_cover cases/assignments/terms/max_terms:",random_cover_tests())
    print("random_signed cases/modes/max_terms:",random_signed_tests())
    print("parity q/clauses/obstruction_terms; zero_modes; signed_modes:",parity_tests())
    print("local_full_parity L/R/clauses/nonempty_left_fibres/right_counts:",local_full_parity_smoke())
    print("PASS: exact finite regressions only; no asymptotic lower bound claimed.")


if __name__ == "__main__":
    main()
