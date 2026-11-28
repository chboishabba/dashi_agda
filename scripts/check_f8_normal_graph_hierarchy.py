"""Original F8 Gaussian-normal operator: exact normal derivative hierarchy.

L u = -dt(A dt u) + dn(B dn u) - C u, A=a^3/N,
B=N a^3, C=N a k^2. Commutators have physical coefficient jets.
This is not a normal-trace, PDE existence, or numerical certification theorem.
"""
from math import comb
import sympy as s


def normal_commutator(u,A,B,C,t,n,m):
    """Return L(dn^m u) - dn^m (L u), exact Leibniz expansion."""
    return sum(comb(m,j)*(s.diff(s.diff(A,n,j)*s.diff(u,t,n,m-j),t)
        -s.diff(s.diff(B,n,j)*s.diff(u,n,m-j+1),n)
        +s.diff(C,n,j)*s.diff(u,n,m-j)) for j in range(1,m+1))


def wave(u,A,B,C,t,n):
    return -s.diff(A*s.diff(u,t),t)+s.diff(B*s.diff(u,n),n)-C*u


def characteristic_identity(t,n,k):
    a=s.sinh(s.asinh(t)-n)
    N=s.cosh(s.asinh(t)-n)/s.sqrt(1+t*t)
    a_t=s.diff(a,t)
    a_n=s.diff(a,n)
    N_n=s.diff(N,n)
    assert s.simplify(a_t-N)==0
    assert s.simplify(a_n+s.sqrt(1+t*t)*N)==0
    W,V,H=[s.Function(x)(t,n) for x in ('W','V','H')]
    # Original R/L characteristic system: V_t=(N W)_n exactly,
    # even off the wave equation and independently of source.
    S=s.Function('S')(t,n)
    R=W+V;L=W-V
    Rt=N*s.diff(R,n)+S+N_n*W
    Lt=-N*s.diff(L,n)+S-N_n*W
    assert s.expand((Rt-Lt)/2-s.diff(N*W,n))==0
    # Defect D=H_n-V has D_t=0 if H_t=N W and characteristic rhs.
    assert s.simplify(s.diff(N*W,n)-(Rt-Lt)/2)==0
    return a,N


def exact():
    t,n,k=s.symbols('t n k',positive=True)
    a,N=characteristic_identity(t,n,k)
    A=a**3/N;B=N*a**3;C=N*a*k*k
    # Independent polynomial manufactured solution; coefficient polynomials
    # are symbolic to avoid relying on an untested library PDE identity.
    U=1+2*t+3*n+4*t*n+5*t*t*n*n+7*n**5
    AA=2+t+n+t*n;BB=3+2*t+3*n+t*n;CC=k*k*(1+t+n*n)
    for m in range(1,5):
        direct=s.expand(wave(s.diff(U,n,m),AA,BB,CC,t,n)-s.diff(wave(U,AA,BB,CC,t,n),n,m))
        comm=s.expand(normal_commutator(U,AA,BB,CC,t,n,m))
        assert s.expand(direct-comm)==0,(m,direct,comm)
    # Exact original-coefficient first normal commutator, all jets retained:
    # L(H_n)=F_n+dt(A_n H_t)-dn(B_n H_n)+C_n H.
    H=s.Function('H')(t,n)
    expression=normal_commutator(H,A,B,C,t,n,1)
    expected=s.diff(s.diff(A,n)*s.diff(H,t),t)-s.diff(s.diff(B,n)*s.diff(H,n),n)+s.diff(C,n)*H
    assert s.expand(expression-expected)==0
    # Higher normal modes need higher boundary values, not only prescribed H_n.
    R=[s.Function(f'r{m}')(t,n) for m in range(5)]
    assert s.diff(R[0],n,3)!=s.diff(R[1],n,3)
    # Exact GN coefficient wave normal derivative at the physical wall.
    gg=s.sqrt(1+t*t)
    assert s.simplify(s.diff(A,n).subs(n,0)-t**4/gg+3*t*t*gg)==0
    assert s.simplify(s.diff(B,n).subs(n,0)+t**4/gg+3*t*t*gg)==0
    assert s.simplify(s.diff(C,n).subs(n,0)+k*k*(t*t/gg+gg))==0
    # Counterexample: source first normal trace alone does not fix H_nn.
    h1=n;h2=n+n*n
    assert s.diff(h1,n).subs(n,0)==s.diff(h2,n).subs(n,0)
    assert s.diff(h1,n,2).subs(n,0)!=s.diff(h2,n,2).subs(n,0)
    print('PASS original GN characteristic integrability, normal commutators m=1..4, boundary nonuniqueness')

if __name__=='__main__': exact()
