"""Full F8 Poincare AdS5 reference covariant harmonic linearization.
All 15 relative metric components, moving wall. Not coupled IBVP acceptance.
"""
import sympy as s
from itertools import product,combinations_with_replacement

D=5;n=4;E=s.diag(-1,1,1,1,1);ids=list(combinations_with_replacement(range(D),2));I=s.eye(15)
def enc(p):return s.Matrix([p[i,j] for i,j in ids])
def dec(v):return s.Matrix(D,D,lambda i,j:v[ids.index(tuple(sorted((i,j))))])
def op(f):return s.Matrix.hstack(*(enc(f(dec(I[:,i]))) for i in range(15)))
def L(a):
    A=s.zeros(D); A[a,n]=-E[a,a];A[n,a]=1
    return A

def lift(A,p):return A*p+p*A.T

def matrices():
    J=[op(lambda p,a=a:lift(L(a),p)) for a in range(n)]
    C=op(lambda p:2*(p-E*s.trace(E*p)))
    V=sum((E[a,a]*J[a]*J[a] for a in range(n)),s.zeros(15))+C
    return J,V

def coeffs(z,v,acc):
    """Coefficient matrices multiplying d_T, d_y, d_xi and zeroth order.
    Principal -d_T²+2v d_T d_y+(1-v²)d_y²+sum d_xi².
    Relative metric perturbation p=z² delta g; z=y+b(T).
    """
    J,V=matrices()
    return -2*J[0]/z,(acc-3/z)*I+2*v*J[0]/z,[2*J[a]/z for a in range(1,n)],V/z**2

def direct_rough(p,x):
    """Independent coordinate Christoffel covariant derivatives, actual h=z^-2 p."""
    z=x[n];g=E/z**2;gi=z**2*E;h=p/z**2;ix=range(D)
    G={(a,b,c):sum(gi[a,l]*(s.diff(g[l,c],x[b])+s.diff(g[l,b],x[c])-s.diff(g[b,c],x[l]))/2 for l in ix) for a,b,c in product(ix,repeat=3)}
    U=[s.Matrix(D,D,lambda i,j:s.expand(s.diff(h[i,j],x[a])-sum(G[l,a,i]*h[l,j]+G[l,a,j]*h[i,l] for l in ix))) for a in ix]
    box=s.zeros(D)
    for a in ix:
        box+=gi[a,a]*s.Matrix(D,D,lambda i,j:s.expand(s.diff(U[a][i,j],x[a])-sum(G[l,a,a]*U[l][i,j]+G[l,a,i]*U[a][l,j]+G[l,a,j]*U[a][i,l] for l in ix)))
    return box.applyfunc(s.expand)

def norm(A):return max(sum(abs(x) for x in A.row(i)) for i in range(A.rows))

def run():
    x=s.symbols('T x1 x2 x3 z',real=True);z=x[n];J,V=matrices();C=op(lambda p:2*(p-E*s.trace(E*p)))
    p=dec(s.Matrix([sum((i+1+a)*x[a]**2+(i-a)*x[a] for a in range(D))+sum((i+a-b)*x[a]*x[b] for a in range(D) for b in range(a+1,D)) for i in range(15)]))
    expected=enc(sum((E[a,a]*p.diff(x[a],2) for a in range(D)),s.zeros(D))-3*p.diff(z)/z)+sum((2*E[a,a]*J[a]*enc(p.diff(x[a]))/z for a in range(n)),s.zeros(15,1))+(V-C)*enc(p)/z**2
    assert (enc(direct_rough(p,x))-expected).applyfunc(s.expand)==s.zeros(15,1)
    # curvature on constant curvature -1, not Euclidean component contraction
    R=s.Matrix(D,D,lambda i,j:sum((-E[i,j]*E[a,b]+E[i,b]*E[a,j])*(E*p*E)[a,b] for a,b in product(range(D),repeat=2)))
    assert (2*enc(R)-C*enc(p)).applyfunc(s.expand)==s.zeros(15,1)
    # Actual moving chart derivative square, no lost acceleration or normal connection term.
    T,y=s.symbols('T y');b=s.Function('b')(T);v=b.diff(T);acc=v.diff(T);u=s.Function('u')(T,y)
    DT=lambda f:f.diff(T)-v*f.diff(y)
    assert s.expand(-DT(DT(u))+u.diff(y,2)+u.diff(T,2)-2*v*u.diff(T,y)-(1-v*v)*u.diff(y,2)-acc*u.diff(y))==0
    a,d,c,e=coeffs(z,v,acc)
    assert a==-2*J[0]/z and c==[2*J[j]/z for j in (1,2,3)]
    assert (d-((acc-3/z)*I-v*a)).applyfunc(s.expand)==s.zeros(15)
    # A decoupled transverse tracefree component: original F8 equation.
    p=s.zeros(5);p[2,3]=p[3,2]=1;pp=enc(p)
    assert V*pp==s.zeros(15,1) and J[0]*pp==s.zeros(15,1) and J[1]*pp==s.zeros(15,1)
    # Liouville change p=z^(3/2)u retains connection potential and removes scalar drift.
    f=s.Function('f')(z)
    assert s.simplify((s.diff(z**s.Rational(3,2)*f,z,2)-3/z*s.diff(z**s.Rational(3,2)*f,z))/z**s.Rational(3,2)-f.diff(z,2)+15*f/(4*z*z))==0
    print('15-component independent covariant rough Laplacian PASS; 7 grouped checks PASS')
    print('connection infinity norms', [norm(A) for A in J], 'potential infinity norm',norm(V))

if __name__=='__main__':run()
