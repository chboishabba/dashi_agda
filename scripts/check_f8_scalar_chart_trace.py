"""Gauge-accessibility obstruction and scaled normal trace estimate.
Necessary chart compatibility, conditional higher-regularity estimate only.
"""
import sympy as s

def exact():
    T,z,x=s.symbols('T z x',real=True); k=s.symbols('k',real=True); q=s.I*k
    A,B,C,D=[s.Function(a)(T,z) for a in ('A','B','C','D')]
    a,b,c=[s.Function(a)(T,z) for a in ('a','b','c')]
    # A=h_TT+h_xx, B=h_Tx, C=h_zx, D=h_Tz, relative conformal metric.
    # Gauge change by covariant flat-frame components a=xi_T,b=xi_z,c=xi_x.
    # Conformal Lie term cancels in A and vanishes in offdiagonal rows.
    change=(A-2*s.diff(a,T)-2*q*c,B-s.diff(c,T)-q*a,C-s.diff(c,z)-q*b,D-s.diff(b,T)-s.diff(a,z))
    def residual(A,B,C,D):
        U=s.diff(B,T)-q*A/2
        V=s.diff(C,T)+s.diff(B,z)-q*D
        return s.expand(s.diff(V,T,2)-q*q*V-2*s.diff(U,T,z))
    O=residual(A,B,C,D)
    assert s.expand(residual(*change)-O)==0
    assert residual(0,0,0,0)==0
    assert s.simplify(O.subs({A:0,B:0,C:0,D:T*z}).doit()-q**3*T*z)==0
    # The necessary chart equations imply the invariant residual vanishes.
    U=s.diff(c,T,2)-q*q*c; V=2*s.diff(c,T,z)
    assert s.expand(s.diff(V,T,2)-q*q*V-2*s.diff(U,T,z))==0
    # Frequency-scaled normal trace. k^2 b^2 f=3 Zn+j, lambda^2=1+k^2.
    b0,lam=s.symbols('b0 lam',positive=True); f,j,v=s.symbols('f j v',real=True)
    assert s.expand(k**4*b0**4*f*f-(3*v+j)**2).subs(v,(k*k*b0*b0*f-j)/3).expand()==0
    assert s.expand(18*v*v+2*j*j-(3*v+j)**2-(3*v-j)**2)==0
    # Apply collar trace to Zn: |Zn(0)|²/lambda <= 2 int Zn² + lambda^-2 int Znn²
    # for d=1/lambda; fixed shorter collar handled by d=min(L,1/lambda).
    a0,a1=s.symbols('a0 a1',nonnegative=True)
    assert s.expand((2*lam*a0+a1/lam)/lam-2*a0-a1/lam**2)==0
    # Exact GN scalar master PDE: solve normal second derivative from time jet.
    t,n=s.symbols('t n',positive=True); Z=s.Function('Z')(t,n); N=s.Function('N')(t,n); R=s.Function('R')(t,n); S=s.Function('S')(t,n)
    box=-s.diff(R**3/N*s.diff(Z,t),t)/(N*R**3)+s.diff(N*R**3*s.diff(Z,n),n)/(N*R**3)-k*k*Z/R**2
    nn=S+s.diff(Z,t,2)/N**2+(3*s.diff(R,t)/R-s.diff(N,t)/N)*s.diff(Z,t)/N**2-(s.diff(N,n)/N+3*s.diff(R,n)/R)*s.diff(Z,n)+k*k*Z/R**2
    assert s.simplify((box-S).subs(s.diff(Z,n,2),nn))==0
    print('8 exact grouped chart / trace checks PASS')
    return O,nn

if __name__=='__main__': exact()
