#!/usr/bin/env python3
"""Exact instantaneous R225/R388 derivative on the existing C=1 donor.

No time stepping or real-trajectory assertion. Same original ordered rows,
exact Q(sqrt2,sqrt3,i) arithmetic. Viscosity nu=1. Run from scripts/.
"""
import json
from collections import defaultdict
from check_ns_r568_physical_source_weld_exact_20261123 import (
    F, Z, VZERO, paired_state, galerkin_nonlinearity, physical_cells,
    m2, vadd, vsub, vmul, reHerm, sumv,
)


def field_add(u, v, t=1):
    return {p: vadd(a, vmul(F(t), v[p])) for p, a in u.items()}


def grouped(rows, value):
    g = defaultdict(list)
    for i, row in enumerate(rows):
        g[row[2]].append(value[i])
    return {r: sumv(v) for r, v in g.items()}


def pairing(A, B):
    return sum((reHerm(a, b)/(r+s) for r, a in A.items()
                for s, b in B.items()), Z)


def row_pairing(rows, A, B):
    return sum((reHerm(a, b)/(rows[i][2]+rows[j][2])
                for i, a in enumerate(A) for j, b in enumerate(B)), Z)


def run():
    counts = dict(states=0, rows=0, Mdot=0, Ddot=0, bucket_rates=0,
                  gram_first=0, gram_second=0, signed_rows=0, nonzero_Ddot=0)
    for seed in (61, 63):
        u = paired_state(seed)
        G = galerkin_nonlinearity(u)
        v = {p: vsub(G[p], vmul(F(m2(p)), a)) for p, a in u.items()}
        # Polarization gives the exact derivative of quadratic N along v.
        Gv = galerkin_nonlinearity(v)
        Gdot = {p: vsub(vsub(w, G[p]), Gv[p]) for p, w in
                galerkin_nonlinearity(field_add(u, v)).items()}
        shifted = {t: field_add(u, v, t) for t in (-2, -1, 1, 2)}
        shifted_G = {t: galerkin_nonlinearity(w) for t, w in shifted.items()}
        neg_u = {p: vmul(F(-1), a) for p, a in u.items()}
        neg_G = galerkin_nonlinearity(neg_u)
        assert neg_G == G
        for k in ((1, 0, 0), (1, 1, 0)):
            rows = physical_cells(u, G, k)
            L = physical_cells(v, G, k)
            R = physical_cells(u, Gdot, k)
            S = {t: physical_cells(w, shifted_G[t], k)
                 for t, w in shifted.items()}
            neg_rows = physical_cells(neg_u, neg_G, k)
            D, M = [r[3] for r in rows], [r[4] for r in rows]
            Md, Dd = [], []
            for i, (p, q, r, d, m) in enumerate(rows):
                assert all(a[i][:3] == (p, q, r) for a in
                           (L, R, neg_rows, *S.values()))
                # Quadratic central difference and cubic-exact 4-point stencil.
                md = vmul(F(1)/2, vsub(S[1][i][4], S[-1][i][4]))
                dd = vmul(F(1)/12, vsub(vmul(F(8), vsub(S[1][i][3], S[-1][i][3])),
                                        vsub(S[2][i][3], S[-2][i][3])))
                assert md == vsub(d, vmul(F(r), m)), ('Mdot', seed, k, p, q)
                assert dd == vadd(L[i][3], R[i][3]), ('Ddot', seed, k, p, q)
                assert neg_rows[i][4] == m and neg_rows[i][3] == vmul(F(-1), d)
                Md.append(md); Dd.append(dd)
                counts['rows'] += 1; counts['Mdot'] += 1; counts['Ddot'] += 1
                counts['signed_rows'] += 1; counts['nonzero_Ddot'] += int(dd != VZERO)
            db, mb, mdb, ddb = (grouped(rows, a) for a in (D, M, Md, Dd))
            for r in mb:
                assert mdb[r] == vsub(db[r], vmul(F(r), mb[r]))
                counts['bucket_rates'] += 1
            f = pairing(db, mb)
            fd = pairing(ddb, mb) + pairing(db, mdb)
            assert f == row_pairing(rows, D, M)
            assert fd == row_pairing(rows, Dd, M) + row_pairing(rows, D, Md)
            # Qraw'=2F-||sum M||²; differentiate once more using same rows.
            Mdd = [vsub(dd, vmul(F(row[2]), md)) for row, dd, md in zip(rows, Dd, Md)]
            mddb = grouped(rows, Mdd)
            q1 = pairing(mdb, mb) + pairing(mb, mdb)
            q2 = pairing(mddb, mb) + F(2)*pairing(mdb, mdb) + pairing(mb, mddb)
            assert q1 == F(2)*f - reHerm(sumv(M), sumv(M))
            assert q2 == F(2)*fd - F(2)*reHerm(sumv(M), sumv(Md))
            counts['gram_first'] += 1; counts['gram_second'] += 1
        counts['states'] += 1
    print(json.dumps(dict(status='PASS', counts=counts,
                          scope='instantaneous algebraic R225/R388; no real-time or uniform estimate'), sort_keys=True))


if __name__ == '__main__':
    run()
