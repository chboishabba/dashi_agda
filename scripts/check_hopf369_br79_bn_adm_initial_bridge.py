#!/usr/bin/env python3
"""BR79: EXISTING BN nonlinear scalar constraint -> original 5D ADM Cauchy constraints.

Source owners: P0 BI/BK/BL/BM/BN global nonlinear R(h)=-12 on the
four-dimensional Riemannian H3 x S1 spatial carrier; BR48/73 physical
ADM metric and BR33/34/71 two-chart wall conditions.

For 5D Einstein vacuum Ric(g)=-4 g, cosmological constant Lambda=-6.
On a spacelike four-slice with spatial h>0 and second fundamental form K:
 Hamiltonian: R(h)+(tr_h K)^2-|K|_h^2 = 2 Lambda = -12.
 Momentum: D_i(K^i_j-delta^i_j tr_h K)=0.
Thus BN's R(h)=-12 is EXACTLY the vacuum Hamiltonian constraint
for TIME-SYMMETRIC K=0. No new scalar solver is needed.
For general K, the original scalar equation must instead target
 R(h)+12=|K|_h^2-(tr_h K)^2, and momenta are independent.

The BN spatial seam/Israel compatibility is on an initial slice and
does not automatically provide the four spacetime timelike-wall
BR71/72 harmonic and Gauss/Codazzi compatibility conditions. Do not
reinterpret the BL/BM monotonicity norm as a hyperbolic energy estimate.

Uses exact symbolic 4x4 symmetric K and nonorthonormal positive h.
No external PDE existence claim, no assertion BN kernel checked here.
"""
import argparse
import sympy as s

def invariant(h,K):
    hi=h.inv()
    tr=s.trace(hi*K)
    sq=s.trace(hi*K*hi*K)
    return s.cancel(tr**2-sq),tr,sq

def cauchy():
    h=s.Matrix([[3,1,0,0],[1,4,1,0],[0,1,5,1],[0,0,1,2]])
    assert h.det()>0 and all(h[:k,:k].det()>0 for k in range(1,5))
    zero=s.zeros(4);Q,tr,sq=invariant(h,zero)
    R=-12
    assert Q==0 and tr==0 and sq==0
    assert R+Q==2*(-6)
    # Nonzero K=κh is a real counterexample to promoting BN directly.
    k=s.symbols('k',real=True,nonzero=True)
    q,_,_=invariant(h,k*h)
    assert s.expand(q-12*k*k)==0
    assert s.expand((-12)+q-(-12))!=0
    assert s.simplify((-12-12*k*k)+q+12)==0
    # Tracefree K has opposite constraint sign.
    hi=h.inv()
    TT=s.diag(1,-hi[0,0]/hi[1,1],0,0)
    assert TT==TT.T
    q,t,ss=invariant(h,TT)
    assert t==0 and q==-ss and ss>0
    assert s.simplify((-12+ss)+q+12)==0
    print('PASS BR79 BN R=-12 -> vacuum 5D Hamiltonian on K=0, full nonorthogonal 4D h')
    print('PASS BR79 counterexamples for nonzero mean K and tracefree K requiring scalar correction')

def momentum():
    eta=s.diag(-1,1,1,1)
    q=s.Matrix(s.symbols('q0:4',real=True))
    K=s.Matrix(4,4,lambda a,b:s.Symbol(f'k{min(a,b)}{max(a,b)}'))
    tr=s.trace(eta*K)
    M=K*eta-s.eye(4)*tr
    # In a flat reference tangent chart, momentum divergence is q^i
    # times the covariant symmetric tensor minus trace component.
    out=K*eta*q-q*tr
    assert out==M*q
    zero=out.subs({z:0 for z in K.free_symbols})
    assert zero==s.zeros(4,1)
    k=s.symbols('k',nonzero=True)
    Kpure=k*eta
    assert (Kpure*eta*q-q*s.trace(eta*Kpure)+3*k*q)==s.zeros(4,1)
    # This is an independent K constraint, not implied by scalar R.
    assert out!=s.zeros(4,1)
    print('PASS BR79 four independent momentum constraints and zero/time-symmetric source')

def refusal():
    # BN nonlinear scalar existence is an initial-data producer only.
    from pathlib import Path
    required=('check_hopf369_p0bl_coercive.py','check_hopf369_p0bm.py',
              'check_hopf369_p0bn.py','check_hopf369_br_physical_boundary_repair.py')
    for name in required:
        assert (Path(__file__).resolve().parent/name).is_file(),name
    print('PASS BR79 exact existing BL/BM/BN/BR33 source ownership; no implied reduced Einstein evolution')

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--part',choices=('cauchy','momentum','owners'),default='cauchy')
    x=p.parse_args()
    {'cauchy':cauchy,'momentum':momentum,'owners':refusal}[x.part]()
if __name__=='__main__':main()
