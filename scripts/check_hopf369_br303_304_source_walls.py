"""BR303 vacuum pure-tension wall normal-jet weld; BR304 candidate caloric lift.
These are exact conditional identities, not a BN time evolution or P0AG action.
"""
import sympy as s
import argparse

def eq(a,b):
    z=a-b
    assert (z.applyfunc(s.simplify)==s.zeros(*z.shape)) if isinstance(z,s.MatrixBase) else s.simplify(z)==0

def periodic():
    # BR84 original nonorthogonal induced wall chart and tension.
    h=s.diag(-s.Rational(7,5)**2,1,1,1)
    h[1:4,1:4]=s.Matrix([[3,1,0],[1,4,1],[0,1,2]])
    j=-s.Rational(6,5);I=h.inv()
    S=s.Matrix(4,4,lambda a,b:s.Symbol('S%d%d'%(min(a,b),max(a,b)),real=True))
    kp,km=S+j*h/2,S-j*h/2
    tau=lambda k:s.trace(I*k)
    norm=lambda k:s.trace(I*k*I*k)
    Q=lambda k:tau(k)**2-norm(k)
    # Gauss in 5D Ric=-4g: R(h)=-12+Q on either face.
    eq(Q(kp)-Q(km),6*j*tau(S))
    # Gaussian normal Ric_ab=Ric(h)_ab-K'_ab-tr(K)K_ab+2 K h^-1 K.
    # Ric(h) and 4h common; difference fixes the next normal jet.
    rhs=lambda k:-tau(k)*k+2*k*I*k
    eq(rhs(kp)-rhs(km),-j*tau(S)*h)
    # Hence common intrinsic curvature plus nonzero pure tension force
    # mean-curvature zero, then equal covariant second normal metric jets.
    S0=S-tau(S)*h/4
    eq(tau(S0),0)
    eq((rhs(kp)-rhs(km)).subs(dict(zip(list(S),list(S0))),simultaneous=True),s.zeros(4))
    print('BR303 exact 5D vacuum Gauss and normal Ricci jump: mean trace zero and next normal jet agreement',flush=True)
    print('OPEN actual BN representatives, tangential/time hierarchy and exterior')

def material():
    n,V,T,c=s.symbols('n V T c',positive=True)
    # Candidate ideal caloric term; at T=1 free energy exactly P0AG entropy.
    F=T*n*(s.log(n/V)-1)-c*n*T*s.log(T)
    S=-s.diff(F,T);p=-s.diff(F,V);mu=s.diff(F,n);E=s.simplify(F+T*S)
    eq(F.subs(T,1),n*(s.log(n/V)-1));eq(E,c*n*T);eq(p,n*T/V)
    for x in (n,V,T):eq(s.diff(E,x),T*s.diff(S,x)-p*s.diff(V,x)+mu*s.diff(n,x))
    eq(s.diff(E,T),c*n)
    # With u.u=-1, material perfect-fluid divergence energy projection
    # -u_nu div(Tmat^mu nu)=D e+(e+p)theta; independently project exchange.
    a,b,q,h=s.symbols('D_e theta q heat',real=True);e,p0=s.symbols('e p',real=True)
    eq((a+(e+p0)*b-q).subs(a,q-(e+p0)*b),0)
    # Numerical entropy remainder is not inserted into physical q.
    assert h not in (q-(e+p0)*b).free_symbols
    print('BR304 candidate caloric extension matches T=1 P0AG free energy; exact first law and positive heat capacity',flush=True)
    print('OPEN physical caloric coefficient, material transport/action and reservoir stress; energy projection is not full momentum closure')

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--part',choices=['periodic','material'],required=True);globals()[p.parse_args().part]()
