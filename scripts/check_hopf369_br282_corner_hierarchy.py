"""BR282: all-order canonical Israel residual inverse, on BR84 corner chart.
Exact formal coefficient arithmetic. Higher wall jets are fixtures, not a
solution of the original nonlinear BN spacetime corner hierarchy.
"""
import sympy as s
from math import factorial


def add(A,B):return [a+b for a,b in zip(A,B)]
def scale(A,B):return [sum((A[i]*B[k-i] for i in range(k+1)),s.zeros(4)) for k in range(len(A))]
def mul(A,B):return [sum((A[i]*B[k-i] for i in range(k+1)),s.zeros(4)) for k in range(len(A))]
def inv(A):
    out=[A[0].inv()]
    for k in range(1,len(A)):out.append(-out[0]*sum((A[i]*out[k-i] for i in range(1,k+1)),s.zeros(4)))
    return out

def tr(A):return [s.trace(a) for a in A]

def trace_reverse(H,J):
    I=inv(H);F=mul(I,J);return add(mul(F,I),scale([-v for v in tr(F)],I))

def density(H):
    I=inv(H);dH=[(i+1)*H[i+1] for i in range(len(H)-1)]+[s.zeros(4)];L=[x/2 for x in tr(mul(I,dH))]
    w=[s.S.One]
    for k in range(1,len(H)):w.append(sum(w[i]*L[k-i-1] for i in range(k))/k)
    return w

def inverse_canonical(H,P,w):
    # Undo volume density, then invert the pointwise raised trace reversal.
    Q=[]
    for k in range(len(H)):Q.append(P[k]-sum((w[i]*Q[k-i] for i in range(1,k+1)),s.zeros(4)))
    M=mul(H,Q);return add(mul(M,H),scale([-v/3 for v in tr(M)],H))


def main():
    # Original BR84 nonorthogonal timelike corner h4 and tension j.
    R=s.Rational;H0=s.diag(-R(7,5)**2,1,1,1);H0[1:4,1:4]=s.Matrix([[3,1,0],[1,4,1],[0,1,2]]);j=-R(6,5)
    N=7
    fixture=lambda k:s.Matrix(4,4,lambda a,b:R(((min(a,b)+1)*7+(max(a,b)+1)*11+k*13)%19-9,23+k))
    H=[H0]+[fixture(k)/factorial(k) for k in range(1,N)];w=density(H)
    # Correct source is j h on every jet; independent jump defects are retained.
    for m in range(N):
        J=[s.zeros(4) if k<m else fixture(k+8) for k in range(N)]
        jump=add([j*h for h in H],J);Jactual=add(jump,[-j*h for h in H]);P=scale(w,trace_reverse(H,Jactual))
        assert inverse_canonical(H,P,w)==J
        assert all(P[k]==s.zeros(4) for k in range(m))
        I0=H0.inv();assert P[m]==I0*J[m]*I0-s.trace(I0*J[m])*I0
    # Independent arbitrary canonical data reverse-solved and re-opened.
    P=[fixture(k+16) for k in range(N)];J=inverse_canonical(H,P,w)
    assert scale(w,trace_reverse(H,J))==P
    # A moving wall is not a fixed-coordinate second derivative.
    t,n,phi,psi=s.symbols('t n phi psi');F=t*t*fixture(1)+t*n*fixture(2)+n*n*fixture(3)+n*fixture(4)
    at={t:0,n:0};moved=F.subs(n,phi*t+psi*t*t/2).diff(t,2).subs(t,0)
    chain=(F.diff(t,2)+2*phi*F.diff(t,n)+phi**2*F.diff(n,2)+psi*F.diff(n)).subs(at)
    assert (moved-chain).applyfunc(s.expand)==s.zeros(4) and chain!=F.diff(t,2).subs(at)
    print('BR282 seven canonical jet levels, exact triangular inverse and moving-wall second chain rule PASS',flush=True)

if __name__=='__main__':main()
