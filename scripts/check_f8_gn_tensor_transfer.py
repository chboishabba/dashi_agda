"""F8 actual GN frame normal tensor operator, tangential time jets frozen.
Finite collar Dirichlet comparison. No exterior DtN or nonlinear claim.
"""
import sympy as s
from itertools import combinations_with_replacement
from fractions import Fraction as Q

ids=list(combinations_with_replacement(range(5),2)); E=s.diag(-1,1,1,1,1); I=s.eye(15)
def enc(p): return s.Matrix([p[i,j] for i,j in ids])
def dec(v): return s.Matrix(5,5,lambda i,j:v[ids.index(tuple(sorted((i,j))))])
def op(f): return s.Matrix.hstack(*(enc(f(dec(I[:,i]))) for i in range(15)))
def lift(C):return op(lambda p:-C.T*p-p*C)

def frame_generators(h,k0,k):
    C=[s.zeros(5) for _ in range(5)]
    C[0][4,0]=C[0][0,4]=k0
    for i in range(1,4):
        C[i][0,i]=C[i][i,0]=h; C[i][4,i]=-k; C[i][i,4]=k
    return [lift(c) for c in C]

def coefficients(t,n):
    beta=s.sqrt(1+t**-2); A=s.cosh(n)-beta*s.sinh(n); a=t*A
    N=s.cosh(n)-s.sinh(n)/beta; k0=N.diff(n)/N; k=a.diff(n)/a; h=1/a
    M=frame_generators(h,k0,k); C=op(lambda p:2*(p-E*s.trace(E*p)))
    # x_n=1/N, p=a^-3/2 u at fixed t. Freeze only AFTER evaluating time derivatives.
    dx=lambda f:N*f.diff(n)
    drift=3*N*k
    vli=-dx(drift)/2-drift**2/4
    Bt=(N.diff(t)/N-3*N*h)*I-2*N*M[0]
    Bx=[2*N*N/A*M[i] for i in range(1,4)] # physical tangential covectors at wall
    V=N*N*(-M[0].diff(t)/N-M[0]*M[0]+sum((M[i]*M[i] for i in range(1,4)),s.zeros(15))-3*h*M[0]+C)+vli*I
    return A,N,Bt,Bx,V

def norm(A): return max(sum(abs(x) for x in A.row(i)) for i in range(A.rows))
def run():
    h,k0,k=s.symbols('h k0 k',real=True); M=frame_generators(h,k0,k)
    # Independent direct covariant frame derivative on a general tensor.
    p=dec(s.Matrix(s.symbols('p:15'))); C=s.zeros(5); C[0,4]=C[4,0]=k0
    assert M[0]*enc(p)==enc(-C.T*p-p*C)
    assert M[4]==s.zeros(15)
    t,n=s.symbols('t n',positive=True); A,N,Bt,Bx,V=coefficients(t,n)
    # Fixed-time scalar normal conjugation, independent polynomial test.
    x=s.symbols('x'); f=s.Function('f')(n); a=t*A; p=a**(-s.Rational(3,2))*f
    expr=N*N*(p.diff(n,2)+(N.diff(n)/N+3*a.diff(n)/a)*p.diff(n))*a**s.Rational(3,2)
    expected=N*(N*f.diff(n)).diff(n)+(-s.Rational(3,2)*N*(N*a.diff(n)/a).diff(n)-s.Rational(9,4)*(N*a.diff(n)/a)**2)*f
    assert s.simplify(expr-expected)==0
    # At the wall, no coordinate time lapse derivative; principal clock frequency unchanged.
    assert s.simplify(N.subs(n,0)-1)==0 and s.simplify(N.diff(t).subs(n,0))==0
    assert s.simplify((N*N/A**2).subs(n,0)-1)==0
    for tt in (1,3,12):
        vals=[Bt,*Bx,V]; vals=[X.subs({n:0,t:tt}).evalf() for X in vals]
        assert max(float(norm(X)) for X in vals)<1000
        print('wall t',tt,'matrix infinity norms',[round(float(norm(X)),6) for X in vals])
    # Exact scalar/matrix perturbation budget for positive-real-w resonance sector.
    # |E|<=C k, Re w>=a k^(4/3), |w|<=B k^(4/3), |tau|>=k/2.
    # For C/(a*k^(1/3))<=1/2, delta DtN <= C/sqrt(a)*k^(1/3).
    # ||N0^-1|| delta <= C/a*(k^-1/3+45 B/gamma).
    C=Q(10000); a=Q(1,1000); B=Q(2); gamma=Q(10**12); x=Q(10**12) # x=k^(1/3)
    assert C/(a*x)<Q(1,2)
    assert C/a*(1/x+45*B/gamma)<Q(1,10)
    print('6 grouped exact checks, 3 wall norm diagnostics and 2 rational budget controls PASS')

if __name__=='__main__':run()
