"""Geometry-constructor energy and off-shell Bianchi receipts. Standard GR identities."""
from pathlib import Path
import sympy as s

def energy():
    # Finite Galerkin Lagrangian L=U_t^T M U_t/2-v U_t^T C U- U^T A U/2,
    # A=(1-v^2)K+k^2 M. Generic symmetric M,A, arbitrary C and derivatives.
    n=2
    vec=lambda name:s.Matrix(s.symbols(f'{name}:{n}'))
    U,V,Utt,F=map(vec,('u','v','acc','f'))
    M=s.Matrix([[s.Symbol('m0'),s.Symbol('m1')],[s.Symbol('m1'),s.Symbol('m2')]])
    A=s.Matrix([[s.Symbol('a0'),s.Symbol('a1')],[s.Symbol('a1'),s.Symbol('a2')]])
    Md=s.Matrix([[s.Symbol('dm0'),s.Symbol('dm1')],[s.Symbol('dm1'),s.Symbol('dm2')]])
    Ad=s.Matrix([[s.Symbol('da0'),s.Symbol('da1')],[s.Symbol('da1'),s.Symbol('da2')]])
    C=s.Matrix(n,n,s.symbols('c:4'));Cd=s.Matrix(n,n,s.symbols('dc:4'));v,vd=s.symbols('speed speed_dot')
    # m_t = -v C^T V-A U+F, m=M V-v C U
    MUtt=-v*C.T*V-A*U+F-Md*V+vd*C*U+v*Cd*U+v*C*V
    edot=(V.T*MUtt+V.T*Md*V/2+V.T*A*U+U.T*Ad*U/2)[0]
    rhs=(V.T*F-V.T*Md*V/2+V.T*(vd*C+v*Cd)*U+U.T*Ad*U/2)[0]
    assert s.expand(edot-rhs)==0
    a,q,w,k,b=s.symbols('a q w k b', real=True);wT=s.symbols('wT',real=True);u=s.symbols('u',real=True)
    # Quadrature-point E' bulk = -partial_T L at fixed U,U_T.
    p=a-v*q
    assert s.expand(-wT*a*a/2+a*q*(vd*w+v*wT)+((1-v*v)*wT-2*v*vd*w)*q*q/2+k*k*wT*u*u/2 - (-wT*(p*p-q*q-k*k*u*u)/2+w*vd*p*q))==0
    print('PASS arbitrary symmetric mass/stiffness, arbitrary cross matrix finite energy identity; same-quadrature pointwise -L_T identity')

def offshell():
    ns={};p=Path(__file__).with_name('check_f8_quadratic_einstein.py');exec(p.read_text().split('# Three nontrivial TT waves')[0],ns)
    T,x,y,w,z=ns['X'];g,inv,B,N=[ns[a] for a in ('g','inv','B','N')]
    # deliberately off-shell spatial tensor, not a vacuum solution
    H=s.diag(0,0,(T*x+z**3)/z**2,-(T*x+z**3)/z**2,0)
    L=ns['linear'](H);Q=ns['quadratic'](H);J=ns['trace_reverse'](L);C=ns['connection'](H)
    raised=inv*H*inv;trL=s.trace(inv*L)
    J2=ns['trace_reverse'](Q)+g*s.trace(raised*L)/2-H*trL/2
    covJ=[ns['cov'](J,a) for a in N]
    rhs=s.Matrix([sum(raised[a,c]*covJ[c][a,b]+inv[a,c]*sum(C[c][d,a]*J[d,b]+C[c][d,b]*J[a,d] for d in N) for a in N for c in N) for b in N])
    div=ns['divergence'](J2)
    assert (div-rhs).applyfunc(s.simplify)==s.zeros(5,1)
    assert ns['divergence'](ns['trace_reverse'](Q))!=s.zeros(5,1)
    print('PASS off-shell contracted Bianchi identity with inverse metric, connection and trace variation; nonzero naive residual control')
if __name__=='__main__': energy();offshell()
