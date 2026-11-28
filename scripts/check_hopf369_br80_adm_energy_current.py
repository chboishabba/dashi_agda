#!/usr/bin/env python3
"""BR80: exact, fast, NONFROZEN ADM normal-frame energy-current identity.

SOURCE WELD: BR48 actual ADM inverse -> BR73 positive normal energy ->
BR76/77 moving material flux. This exact two-coordinate sector is the
(t,normal) subfamily of the actual 5D metric with three fixed positive
spectator spatial directions. It has independently varying lapse N,
normal spatial scale a=sqrt(H_nn), and normal shift v. No physical
Einstein field equations or boundary well-posedness are assumed.

For w=u_t-v u_n, q=u_n:
 E=(w²/N²+q²/a²)/2,
 J^t=-a E,
 J^n=v a E+q w/a,
 sqrt|g| Box_g u = -∂t(a w/N)+∂n(a v w/N+N q/a).
Then the full exact, NONFROZEN positive normal-frame energy law is
 ∂t J^t+∂n J^n
   = sqrt|g| Box_g u * w/N
     +(a_t-v a_n-a v_n) E - (N_n/(N a)) w q.
This formula includes arbitrary independent first jets of the
actual lapse, spatial metric, shift and all second field derivatives.
Mixed u_tn = u_nt is the ONLY integrability assumption. The last
two terms are precisely the ADM deformation work, not an invented
right-hand side or a scalar coercivity estimate.

The identity follows both from exact current differentiation and from
independent contraction of the original stress T^mu_nu with future
slice-normal X=(1,-v)/N. Full 15+5 component energies are sums of this
scalar principal current; BR15/BR55 curvature/connection and actual
BR71/72 boundary compatibility remain independent source obligations.

This is a mathematical first-jet identity and runnable acceptance,
NOT a full variable-coefficient Einstein-Israel PDE theorem.
"""
import argparse
import sympy as s

N,a,v,p,q=s.symbols('N a v p q',nonzero=True,real=True)
Nt,Ny,at,ay,vt,vy,pt,pn,qt,qn=s.symbols(
    'Nt Ny at ay vt vy pt pn qt qn',real=True)
base=(N,a,v,p,q)
tt=(Nt,at,vt,pt,qt)
yy=(Ny,ay,vy,pn,qn)
def dt(f):return sum(s.diff(f,x)*dx for x,dx in zip(base,tt))
def dn(f):return sum(s.diff(f,x)*dx for x,dx in zip(base,yy))
w=p-v*q
E=(w*w/N**2+q*q/a**2)/2
Jt=-a*E
Jn=v*a*E+q*w/a
waveD=-dt(a*w/N)+dn(a*v*w/N+N*q/a)
deformation=(at-v*ay-a*vy)*E-Ny*w*q/(N*a)

def current():
    residual=dt(Jt)+dn(Jn)-waveD*w/N-deformation
    # Must use actual mixed field jet integrability pn=qt.
    assert s.factor(residual.subs(pn,qt))==0
    # Without the mixed-jet identity the current need not cancel.
    assert s.factor(residual)!=0
    print('PASS BR80 exact variable ADM normal current and true deformation first-jet source')

def stress():
    G=s.Matrix([[-N*N+a*a*v*v,a*a*v],[a*a*v,a*a]])
    Gi=s.Matrix([[-1/N**2,v/N**2],[v/N**2,1/a**2-v*v/N**2]])
    X=s.Matrix([1,-v])/N
    d=s.Matrix([p,q])
    assert (G*Gi-s.eye(2)).applyfunc(s.cancel)==s.zeros(2)
    norm=(d.T*Gi*d)[0]
    T=d*d.T-G*norm/2
    Tup=Gi*T*Gi
    current=s.Matrix([N*a*(Tup*G*X)[i] for i in range(2)])
    assert s.factor(current[0]-Jt)==0
    assert s.factor(current[1]-Jn)==0
    assert s.factor((X.T*T*X)[0]-E)==0
    # The stress current is exactly the spatial-slice volume-weighted
    # normal frame energy, including shift.
    assert s.factor(-current[0]-a*E)==0
    print('PASS BR80 original ADM stress source and positive normal-frame current equality')

def source():
    # Independent rational first-jet witnesses with nonzero lapse,
    # shift and spatial derivatives, including source negative control.
    for seed in range(1,9):
        v0={N:s.Rational(7+seed,3),
            a:s.Rational(9+seed,5),v:s.Rational(seed-3,7),
            p:s.Rational(2+seed,11),q:s.Rational(seed-5,13),
            Nt:s.Rational(seed,17),Ny:s.Rational(1+seed,19),
            at:s.Rational(2+seed,23),ay:s.Rational(seed-4,29),
            vt:s.Rational(seed+1,31),vy:s.Rational(seed-2,37),
            pt:s.Rational(seed+2,41),pn:s.Rational(seed+3,43),
            qt:s.Rational(seed+3,43),qn:s.Rational(seed+4,47)}
        lhs=(dt(Jt)+dn(Jn)-waveD*w/N).subs(v0)
        rhs=deformation.subs(v0)
        assert lhs==rhs
        if seed==2:assert rhs!=0
    print('PASS BR80 eight exact non-frozen rational ADM source jets and nonzero deformation')

def refusal():
    # A positive principal bulk energy is not boundary dissipation.
    # For a nonzero material tilt the moving flux differs from the
    # fixed Gaussian normal-velocity product (BR76/77).
    G=s.Matrix([[-N*N+a*a*v*v,a*a*v],[a*a*v,a*a]])
    Gi=s.Matrix([[-1/N**2,v/N**2],[v/N**2,1/a**2-v*v/N**2]])
    F=s.Matrix([s.Rational(-1,3),1])
    conormal=(F.T*Gi*s.Matrix([p,q]))[0]
    assert s.factor(conormal-q/a**2)!=0
    # The correct wall flux still needs the full physical K/h/gauge
    # and BR29 constrained transmission, not scalar bulk positivity.
    print('PASS BR80 REFUSAL: nonzero moving-wall conormal is not fixed normal derivative')

if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--part',choices=('current','stress','source','refusal'),default='current')
    x=parser.parse_args()
    {'current':current,'stress':stress,'source':source,'refusal':refusal}[x.part]()
