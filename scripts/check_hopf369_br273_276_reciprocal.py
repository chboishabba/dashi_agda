"""Exact endpoint welds; conditional analytic proof is in roadmap."""
import sympy as s
from itertools import combinations, permutations

def maxwell():
    a,h1,h2,h3=s.symbols('alpha h1 h2 h3', positive=True)
    h=s.diag(h1,h2,h3); r=s.sqrt(h.det()); b=s.Matrix(s.symbols('b:3',real=True)); D=s.Matrix(s.symbols('D:3',real=True)); B=s.Matrix(s.symbols('B:3',real=True)); v=s.Matrix(s.symbols('v:3',real=True))
    F=s.Matrix(3,3,lambda i,j:sum(s.LeviCivita(i,j,k)*B[k] for k in range(3)))
    E=(-v-F*b)/a
    L=a/2*(r*(E.T*h.inv()*E)[0]-(B.T*h*B)[0]/r)
    pi=s.Matrix([s.diff(L,x) for x in v]); sub=dict(zip(v,-a*h*D/r-F*b))
    assert (pi.subs(sub,simultaneous=True)+D).applyfunc(s.simplify)==s.zeros(3,1)
    H=a*((D.T*h*D)[0]+(B.T*h*B)[0])/(2*r)+D.dot(b.cross(B))
    assert s.simplify(((pi.dot(v)-L).subs(sub,simultaneous=True)-H))==0
    rho=((D.T*h*D)[0]+(B.T*h*B)[0])/(2*r*r)
    assert s.simplify(s.diff(H,a)-r*rho)==0
    assert (s.Matrix([s.diff(H,x) for x in b])-B.cross(D)).applyfunc(s.simplify)==s.zeros(3,1)
    for i,x in enumerate((h1,h2,h3)):
        stress=rho/x-(D[i]**2+B[i]**2)/r**2
        assert s.simplify(s.diff(H,x)+a*r*stress/2)==0
    print('BR273 Maxwell Legendre sign, lapse, shift and diagonal metric stress PASS')

def cube():
    # Three affine arrows on signed marked observation: chart x, reflection y, fixed history z.
    q,e,k,dq,de=s.symbols('q e k dq de'); x=lambda p:p; y=lambda p:(p[0],k-p[1]); z=lambda p:(p[0]+dq,p[1]+de); ops=[x,y,z]; p=(q,e)
    def residual(a,b,p):return tuple(s.expand(u-v) for u,v in zip(b(a(p)),a(b(p))))
    for i,j in combinations(range(3),2):
        l=3-i-j
        for base in (p,ops[l](p)):
            R=residual(ops[i],ops[j],base)
            assert R==((0,2*de) if (i,j)==(1,2) else (0,0))
    for order in permutations(range(3)):
        t=p
        for i in order:t=ops[i](t)
        assert s.expand(t[0]-q-dq)==0
        assert s.expand(t[1]-(k-e+de if order.index(1)<order.index(2) else k-e-de))==0
    print('BR274 six marked affine faces and six paths PASS; physical arrow attachment not inferred')

if __name__=='__main__':maxwell();cube()
