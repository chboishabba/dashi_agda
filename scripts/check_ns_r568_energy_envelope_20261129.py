#!/usr/bin/env python3
"""Original C=1 R568 signed finite-flow envelope; exact rational referee.
The analytic proof is in the companion roadmap; no numerical ODE simulation.
"""
import json
from fractions import Fraction as Q
from math import isqrt
from check_ns_r568_physical_source_weld_exact_20261123 import (
    F, Z, paired_state, galerkin_nonlinearity, physical_cells,
    m2, vsub, vadd, vmul, reHerm, exact_real_interval,
)
from check_ns_r568_dynamic_helical_weld_20261129 import (
    grouped, pairing, field_add,
)


def ceilroot(x):
    x = Q(x)
    a = isqrt(x.numerator // x.denominator)
    return a if a*a == x else a+1


def constants(C, E, nu=1):
    # E bounds l2 velocity norm, nonzero cube, helical projectors contractions.
    a = 2*C*ceilroot((2*C+1)**3-1)
    G = a*E**2
    V = G+nu*3*C*C*E
    M = 4*E**2
    D = 8*E*G
    Md = D+nu*6*C*C*M
    Dd = 24*a*E**2*V
    L = Q(Dd*M+D*Md, 2*nu)
    return dict(a=a, G=G, V=V, M=M, D=D, Md=Md, Dd=Dd, L=L)


def upper_abs(z):
    a,b = exact_real_interval(z)
    return max(abs(a),abs(b))


def run():
    out=[]
    for seed in (61,63):
        u=paired_state(seed)
        G=galerkin_nonlinearity(u)
        # Exact energy cancellation and original velocity direction.
        energy=sum((reHerm(v,v) for v in u.values()),Z).scalar()
        assert sum((reHerm(u[p],G[p]) for p in u),Z)==Z
        E=ceilroot(energy)
        b=constants(1,E)
        V={p:vsub(G[p],vmul(F(m2(p)),v)) for p,v in u.items()}
        NV=galerkin_nonlinearity(V)
        dG={p:vsub(vsub(w,G[p]),NV[p]) for p,w in
            galerkin_nonlinearity(field_add(u,V)).items()}
        assert sum((reHerm(v,v) for v in G.values()),Z).scalar()<=b['G']**2
        assert sum((reHerm(v,v) for v in V.values()),Z).scalar()<=b['V']**2
        assert sum((reHerm(v,v) for v in dG.values()),Z).scalar()<=(2*b['a']*E*b['V'])**2
        for k in ((1,0,0),(1,1,0)):
            rows=physical_cells(u,G,k)
            left=physical_cells(V,G,k)
            right=physical_cells(u,dG,k)
            M=[r[4] for r in rows];D=[r[3] for r in rows]
            Md=[vsub(d,vmul(F(r[2]),m)) for r,d,m in zip(rows,D,M)]
            Dd=[vadd(a[3],c[3]) for a,c in zip(left,right)]
            mb,db,mdb,ddb=(grouped(rows,x) for x in (M,D,Md,Dd))
            f=pairing(db,mb)
            fd=pairing(ddb,mb)+pairing(db,mdb)
            gram=pairing(mb,mb)
            assert upper_abs(fd)<=b['L']
            assert upper_abs(gram)<=Q(16)*energy**2/m2(k)
            lo,hi=exact_real_interval(f)
            assert lo>0 or hi<0
            margin=lo if lo>0 else -hi
            T=min(Q(1),margin/(2*b['L']))
            # Whole actual real trajectory, by energy + derivative bound:
            # f(0)-L*t <= f(t) <= f(0)+L*t.
            ilow=lo*T-b['L']*T*T/2
            ihigh=hi*T+b['L']*T*T/2
            assert (ilow>0 if lo>0 else ihigh<0)
            # Independent fixed-output integrated bound follows from Gram FTC;
            # Q>=0 and integral |sum M|^2 <= 4 E0^4 for nu=1.
            global_upper=Q(8)*energy**2/m2(k)+Q(2)*energy**2
            assert ilow<=global_upper
            out.append(dict(seed=seed,k=k,energy=str(energy),E=E,
                F_interval=[str(lo),str(hi)],L=str(b['L']),T=str(T),
                integral_interval=[str(ilow),str(ihigh)],
                fixed_output_upper=str(global_upper),sign=1 if lo>0 else -1))
    print(json.dumps(dict(status='PASS',cases=out),indent=2))


if __name__=='__main__':
    run()
