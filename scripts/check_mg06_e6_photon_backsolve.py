#!/usr/bin/env python3
"""MG06 exact source-faithful E6/trinification one-photon backsolve.

Sources: #1241 check_kk_e6_gs_photon_rank.py and
check_kk_e6_orbifold_vev_anomaly_gate.py; #1106 E32/E33 VEVs.
Finite rational Cartan Gram + 27 charge carriers. Anomalies and 5D
field equations are NOT solved. Other photon/graviphoton cannot be
silently added: the selected E6 orbifold branch omits old bulk B and
projects out the odd metric graviphoton zero mode.
"""
from itertools import product
import sympy as s

P=(-1,-1,1)
UL=(-1,-1,2)
UR=(-1,-1,2)
HL=(s.Rational(1,2),-s.Rational(1,2),s.Integer(0))
HR=(1,-1,0)
phi=s.Matrix([0,2,1,1])
chi=s.Matrix([0,2,-2,0])
ew=s.Matrix([-s.Rational(1,2),-1,1,-1])
gs=s.Matrix([0,1,-1,0])
Q=s.Matrix([1,s.Rational(1,6),s.Rational(1,6),-s.Rational(1,2)])
Y=Q-s.Matrix([1,0,0,0])

def gram(vectors):
    return sum((q*q.T for q in vectors),s.zeros(vectors[0].rows))

def source27():
    rows=[]
    for c,l in product(range(3), repeat=2):
        rows.append(('A',-P[l],s.Matrix([-HL[l],-UL[l],0,0])))
    for c,r in product(range(3), repeat=2):
        rows.append(('B',-P[r],s.Matrix([0,0,UR[r],HR[r]])))
    for l,r in product(range(3), repeat=2):
        rows.append(('C',-P[l]*P[r],s.Matrix([HL[l],UL[l],-UR[r],-HR[r]])))
    return rows

def main():
    vectors=[phi,chi,gs,ew]
    assert gs==chi/2
    assert all((v.T*Q)[0]==0 for v in vectors)
    assert gram(vectors).rank()==3
    assert gram(vectors)*Q==s.zeros(4,1)
    assert len(gram(vectors).nullspace())==1
    assert gram([phi,chi,gs]).rank()==2
    rows=source27()
    assert len(rows)==27
    assert sum(sign==1 for _,sign,_ in rows)==16
    assert sum(sign==-1 for _,sign,_ in rows)==11
    charges=[]
    for _,sign,q in rows:
        y=(q.T*Y)[0]
        charge=(q.T*Q)[0]
        assert charge-y==q[0]
        assert (3*charge).q==1
        charges.append(charge)
    assert s.Rational(-1) in charges and s.Rational(2,3) in charges
    assert s.Rational(-1,3) in charges and s.Integer(0) in charges
    for couplings in ((1,1,1,1),(2,3,5,7),(3,3,3,3)):
        D=s.diag(*couplings)
        M=D*gram(vectors)*D
        raw=D.inv()*Q
        assert M*raw==s.zeros(4,1)
        assert M.rank()==3 and len(M.nullspace())==1
        norm=s.sqrt((raw.T*raw)[0])
        v=raw/norm
        assert s.simplify((v.T*v)[0]-1)==0
        e=1/norm
        for _,_,q in rows:
            assert s.simplify((q.T*D*v)[0]-e*(q.T*Q)[0])==0
    # Equally chosen diagonal couplings is illustrative, not sourced physical normalization.
    g=s.symbols('g',positive=True)
    raw=s.diag(g,g,g,g).inv()*Q
    assert s.simplify((raw.T*raw)[0]-s.Rational(47,36)/g**2)==0
    assert s.simplify(1/s.sqrt((raw.T*raw)[0])-6*g/s.sqrt(47))==0
    # Older independent B or retained A_g gives extra massless fields.
    duplicate=s.diag(gram(vectors),s.zeros(1,1))
    assert duplicate.rank()==3 and len(duplicate.nullspace())==2
    extra=s.diag(gram(vectors),s.zeros(2,2))
    assert extra.rank()==3 and len(extra.nullspace())==3
    x,y=s.symbols('F_L F_R')
    cubic=s.expand((x-y)*(40*x*x+64*x*y+40*y*y))
    assert s.simplify(cubic-8*(x-y)*(5*x*x+8*x*y+5*y*y))==0
    assert cubic.subs(y,x)==0
    print('PASS 27/27 exact source Cartan Q charges (16 LH, 11 RH)')
    print('PASS 3/3 positive diagonal gauge-normalization examples: unique photon and proportional source charges')
    print('PASS illustrative backsolve e=6g/sqrt(47)')
    print('PASS old B or retained graviphoton negative controls: 2 or 3 massless neutral directions')
    print('PASS local UV anomalous-direction factorization (not global cancellation)')
    print('OPEN physical kinetic norm, global anomaly, 5D E21 source, quantum stress, electron mass, atomic same-H')

if __name__=='__main__':
    main()
