"""KK cone and inverse-symbol checks, exact local algebra; no TSFV measurement."""
import sympy as s
from itertools import combinations

def audit():
    # Arbitrary base and positive fibre block: selected exact rational regressions
    # for both one and two compact directions, including mixed time components.
    g=s.Matrix([[-3,1,0,0],[1,4,1,0],[0,1,5,1],[0,0,1,6]])
    for m in (1,2):
        A=s.Matrix(m,4,lambda i,j:s.Rational((i+1)*(j+2),7+i+j))
        R=s.eye(m)*2+s.ones(m,m)/3
        B=s.eye(4).row_join(s.zeros(4,m)).col_join(A.row_join(s.eye(m)))
        P=s.diag(g,R); G=B.T*P*B
        assert B.det()==1 and G.det()==g.det()*R.det()
        assert G.inv()==B.inv()*P.inv()*B.inv().T
        p=s.Matrix(s.symbols('p:4')); k=s.Matrix(s.symbols('k:'+str(m)))
        cov=p.col_join(k); shifted=p-A.T*k
        assert s.expand((cov.T*G.inv()*cov)[0]-(shifted.T*g.inv()*shifted)[0]-(k.T*R.inv()*k)[0])==0
        assert (G.inv()[:4,:4])==g.inv()
        v=s.Matrix(s.symbols('v:4')); w=s.Matrix(s.symbols('w:'+str(m))); V=v.col_join(w)
        assert s.expand((V.T*G*V)[0]-(v.T*g*v)[0]-((w+A*v).T*R*(w+A*v))[0])==0
        print('PASS KK shear, determinant, tangent/dual symbol, horizontal covector',m,flush=True)
    # A finite set of null vectors determines a symmetric Lorentz form up to scale.
    for d in (3,4,5):
        n=d+1; pairs=list(combinations(range(n),2)); E=s.eye(n)
        probes=[E[:,0]+sign*E[:,i] for i in range(1,n) for sign in (-1,1)]
        probes += [E[:,0]+s.Rational(3,5)*E[:,i]+s.Rational(4,5)*E[:,j] for i,j in combinations(range(1,n),2)]
        M=s.Matrix([[v[i]**2 for i in range(n)]+[2*v[i]*v[j] for i,j in pairs] for v in probes])
        assert M.rank()==n*(n+1)//2-1 and len(M.nullspace())==1
        assert M*s.Matrix([-1]+[1]*d+[0]*len(pairs))==s.zeros(len(probes),1)
        print('PASS null-cone conformal tomography',d,1,'rank',M.rank(),'probes',len(probes),flush=True)
    # Diagonal signs do not determine inertia without a principal-axis premise.
    C=s.diag(-1,1,1,1); C[1,2]=C[2,1]=2
    assert C.eigenvals()=={-1:2,1:1,3:1}
    # Two time axes: a single time-coordinate arrow does not restore convexity.
    J=s.diag(-1,-1,1,1); x=s.Matrix([1,2,2,0]); y=s.Matrix([1,-2,2,0])
    Q=lambda v:(v.T*J*v)[0]
    assert Q(x)==Q(y)==-1 and Q(x+y)==12
    # Fibre-null roots for timelike horizontal direction, keep both signs.
    a,r,q,z=s.symbols('a r q z',real=True); p=s.symbols('p',positive=True)
    expr=q+r*(z+a)**2
    for sign in (-1,1):assert s.expand(expr.subs({z:-a+sign*p,q:-r*p*p}))==0
    assert s.expand(((-a+p)+(-a-p))/2+a)==0
    assert s.expand(((-a+p)-(-a-p))**2/4-p*p)==0
    print('PASS diagonal-sign and two-time nonconvexity controls; signed null-root BIDI',flush=True)

if __name__=='__main__':audit()
