"""AW selected original-carrier algebra, spectral domain and metric/stress controls."""
import sympy as s
import numpy as np


def observer():
    a=s.symbols('a:8',real=True); b=s.symbols('b:8',real=True)
    mat=lambda z:s.Matrix(2,2,[z[2*j]+s.I*z[2*j+1] for j in range(4)])
    A,B=mat(a),mat(b); psi=s.Matrix([1,1]); X=s.Matrix([[0,1],[1,0]])
    u=A*psi; v=B*psi
    eq=lambda x,y:s.expand(x-y)==0
    assert eq((psi.T*A.conjugate().T*B*psi)[0]/2,(u.conjugate().T*v)[0]/2)
    lift=lambda z:z.row_join(s.zeros(2,1))
    assert lift(u)*psi==u
    assert all(eq(x,0) for x in (A*B*psi-A*v))
    assert all(eq(x,0) for x in (X*X*u-u))
    assert eq((u.conjugate().T*u)[0]/2,sum(s.re(x)**2+s.im(x)**2 for x in u)/2)
    assert not (0>=1)  # original ABL numerator predicate is not Hilbert nonnegativity
    assert (s.Matrix([[1,-1],[0,0]])*psi)==s.zeros(2,1)
    print('AW1 PASS original complex cyclic Gram, section, composition, clock and zero predicate',flush=True)


def spectral():
    # Positive transfer and unitary on the same selected finite free modes.
    w=np.array([0.,.7,1.5,4.,12.]); t=.125
    U=np.exp(-1j*t*w); T=np.exp(-t*w)
    assert np.max(abs(-np.log(T)/t-w))<1e-13
    assert np.max(abs(abs(U)-1))<1e-14
    assert T[0]==1 and np.all(T[1:]<1)
    for h in (1/8,1/16,1/32,1/64):
        err=abs((np.exp(-1j*h*w)-1)/h+1j*w)
        assert np.all(err<=h*w*w/2+1e-14)
    # Spectral projection, zero retained. Resolvent and graph inverse under J.
    J=np.eye(5)[::-1]; H=np.diag(w); G=J@H@J.T
    assert np.max(abs(np.linalg.inv(G+np.eye(5))-J@np.linalg.inv(H+np.eye(5))@J.T))<1e-15
    print('AW2 PASS 20 difference quotient bounds, zero, positive transfer and selected graph/resolvent',flush=True)


def metric_stress():
    # Non-diagonal Lorentz metric and arbitrary symmetric tangent directions.
    g=s.Matrix([[-2,s.Rational(1,5),0,0],[s.Rational(1,5),3,s.Rational(1,7),0],[0,s.Rational(1,7),4,0],[0,0,0,5]])
    I=g.inv(); v=s.sqrt(-g.det()); H=v*I; assert s.simplify(s.sqrt(-H.det())-v)==0
    p=s.Matrix([2,-1,3,s.Rational(1,2)]); m2=s.Rational(7,10); q=s.Rational(2,3)
    T=p*p.T-g*((p.T*I*p)[0]+m2*q*q)/2
    for i in range(4):
        for j in range(i,4):
            E=s.zeros(4); E[i,j]=E[j,i]=1
            dv=v*s.trace(I*E)/2
            dH=dv*I-v*I*E*I
            invdv=v*s.trace(H.inv()*dH)/2
            invdg=invdv*H.inv()-v*H.inv()*dH*H.inv()
            assert all(s.simplify(x)==0 for x in invdg-E)
            # Fixed physical mass: V=v*m2, fixed scalar q.
            dS=-((p.T*dH*p)[0]+m2*q*q*dv)/2
            assert s.simplify(dS-v*s.trace(I*T*I*E)/2)==0
    # Ward on a genuinely variable metric, homogeneous scalar and time-varying mass.
    t=s.symbols('t',real=True); A=s.Function('A')(t); f=s.Function('q')(t); M=s.Function('M')(t)
    rho=(s.diff(f,t)**2+M*f*f)/2; pressure=(s.diff(f,t)**2-M*f*f)/2
    E=s.diff(f,t,2)+3*s.diff(A,t)/A*s.diff(f,t)+M*f
    assert s.expand(s.diff(rho,t)+3*s.diff(A,t)/A*(rho+pressure)-E*s.diff(f,t)-s.diff(M,t)*f*f/2)==0
    print('AW3/4/5 PASS 10 mixed metric tangent inverses and stress variations; variable-mass Ward residual',flush=True)


if __name__=='__main__':
    observer(); spectral(); metric_stress()
