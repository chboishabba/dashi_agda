"""Round 15 exact algebraic regressions. Not native kernel acceptance.
Euclidean controls integrate a transverse Gaussian-polynomial Fourier
fixture, not an NSE trajectory. Quaternion controls use unit rational
rotations, not the actual CMP102 selected source word.
"""
import sympy as S
from fractions import Fraction as Q
from random import Random
from itertools import product
from functools import lru_cache
from math import prod
if not __debug__:raise SystemExit('refusing optimized execution')

def bsd():
    x,r,s,t,z=S.symbols('x r s t z');e=[x-r*r,x-s*s,x-t*t];y=-r*s*t
    R=[r,s,t];X=x+r*s+s*t+t*r;Y=-(r+s)*(s+t)*(t+r)
    line=-y-(r+s+t)*(z-x)
    c=0
    for i in range(3):
        j,k=[j for j in range(3) if j!=i]
        assert S.expand(X-e[i]-(R[i]+R[j])*(R[i]+R[k]))==0;c+=1
        assert S.cancel(Y/(X-e[i])+r+s+t-R[i])==0;c+=1
    assert S.expand(Y**2-prod(X-a for a in e))==0;c+=1
    assert S.expand(prod(z-a for a in e)-line**2-(z-X)**2*(z-x))==0;c+=1
    assert S.expand(line.subs(z,X)-Y)==0;c+=1
    # Four distinct signed half addresses of a nonexceptional split point.
    rng=Random(36915)
    for _ in range(64):
        R=rng.sample(range(1,30),3);xx=Q(10);ee=[xx-a*a for a in R];yy=-prod(R);halves=set()
        for f,g in product((-1,1),repeat=2):
            a,b,d=R[0]*f,R[1]*g,R[2]*f*g
            U=xx+a*b+b*d+d*a;V=-(a+b)*(b+d)*(d+a)
            assert V!=0;c+=1
            assert V*V==prod(U-z for z in ee);c+=1
            m=-(a+b+d);assert m*m+sum(ee)-2*U==xx;c+=1
            assert -V-m*(xx-U)==yy;c+=1
            for h,E in zip((a,b,d),ee):assert V/(U-E)-m==h;c+=1
            halves.add((U,V))
        assert len(halves)==4;c+=1
    return c

def hodge():
    d=S.symbols('d');f=d*d+S.Rational(16113,16);a=S.Integer(1);v=S.Integer(2);x=v+a/v;s=(1-d)/4;y=v**7
    Q0=-3*a**3-3*a*a*s-a*a+3*a*s+3*a-2*s*s+s+3
    D=x**7-7*a*x**5+14*a*a*x**3-7*a**3*x
    checks=[v*v-x*v+a,D-Q0,D-y-a**7/y,-3*a*a+3*a+1-4*s-d]
    for p in checks:assert S.rem(S.expand(p),f,d)==0
    den=2**6*d**6*(a*v*(v*v-a))**6
    assert S.rem(den,f,d)!=0
    assert y*y!=a**7
    # The fold branch is precisely the base discriminant, after inverting v.
    A,V=S.symbols('A V');X=V+A/V
    assert S.cancel((V*V-A)**2-V*V*(X*X-4*A))==0
    return len(checks)+3

def ns():
    p=S.Matrix(S.symbols('p0:3'));q=S.Matrix(S.symbols('q0:3'));k=p+q
    a=S.Matrix([1,2,3]);b=S.Matrix([2,-1,1]);e=S.Matrix([1,0,2]);A=lambda x:x.cross(a)+x.dot(b)**2*x.cross(e)
    Up,Uq,Uk=A(p),A(q),A(k)
    C=S.expand(q.dot(Up)*Uq.dot(Uk))
    # Fourier U(p)=i A(p) exp(-sum lambda p^2), lambda=(1,2,3).
    # The real cell is C times a common Gaussian, invariant under flip.
    T=dict(zip(list(p)+list(q),list(-p)+list(k)))
    assert S.expand(p.dot(Up))==0
    assert S.expand(C.xreplace(T)+C)==0
    w=lambda x:x.dot(x)
    D=S.expand(w(k)*C);E=S.expand(w(q)*C)
    assert S.expand(D.xreplace(T)+E)==0
    # Gaussian expectation of each 2-dimensional pair (p_i,q_i)
    # uses covariance [[1/3,-1/6],[-1/6,1/3]] / lambda_i.
    @lru_cache(None)
    def moment(i,m,n):
        if m<0 or n<0:return Q(0)
        if m+n==0:return Q(1)
        if m+n==1:return Q(0)
        c=Q(1,3*(i+1));d=Q(-1,6*(i+1))
        if m:return (m-1)*c*moment(i,m-2,n)+n*d*moment(i,m-1,n-1)
        return (n-1)*c*moment(i,m,n-2)
    def expect(z):
        return sum(Q(coeff)*prod(moment(i,M[i],M[i+3]) for i in range(3)) for M,coeff in S.Poly(z,*list(p),*list(q)).terms())
    d,e=expect(D),expect(E);assert d==-e
    assert expect(S.expand((w(k)-w(q))*C))==2*d
    # Same signed numerator even at zero/equal radii; use exact integer vectors.
    count=5;rng=Random(36915)
    for _ in range(1000):
        P=[rng.randrange(-5,6) for i in range(3)];Qv=[rng.randrange(-5,6) for i in range(3)];K=[a+b for a,b in zip(P,Qv)]
        mp,mq,mk=[sum(a*a for a in V) for V in (P,Qv,K)]
        assert mk-mq==mp+2*sum(a*b for a,b in zip(P,Qv));count+=1
        # The nonnegative fourth roots have the same ordering as their masses.
        assert (mk>=mq)==(mp+2*sum(a*b for a,b in zip(P,Qv))>=0);count+=1
    print('Gaussian normalized weighted integral',d)
    return count

def ym():
    def dot(a,b):return sum(x*y for x,y in zip(a,b))
    def mul(a,b):
        x,u,v,w=a;y,i,j,k=b
        return (x*y-u*i-v*j-w*k,x*i+u*y+v*k-w*j,x*j-u*k+v*y+w*i,x*k+u*j-v*i+w*y)
    def q(t,n):
        return ((1-t*t)/(1+t*t),*(2*t/(1+t*t)*a for a in n))
    dirs=[(Q(1),Q(0),Q(0)),(Q(0),Q(1),Q(0)),(Q(3,5),Q(4,5),Q(0)),(Q(0),Q(5,13),Q(12,13))]
    rng=Random(74148);count=0
    for _ in range(256):
        t=Q(rng.randrange(1,9),100);s=Q(rng.randrange(1,9),100);a=q(t,rng.choice(dirs));b=q(s,rng.choice(dirs));z=mul(a,b)
        assert dot(a,a)==dot(b,b)==dot(z,z)==1;count+=1
        sa=2*t/(1+t*t);sb=2*s/(1+s*s)
        assert z[0]>=a[0]*b[0]-sa*sb;count+=1
        X=(Q(0),*a[1:]);H=(Q(0),*b[1:]);ad=tuple(x-y for x,y in zip(mul(X,H),mul(H,X)))
        assert ad[0]==0;count+=1
        assert dot(ad,ad)==4*(dot(X,X)*dot(H,H)-dot(X,H)**2);count+=1
        assert dot(ad,ad)<=4*dot(X,X)*dot(H,H);count+=1
    return count

if __name__=='__main__':
    results=dict(bsd=bsd(),hodge=hodge(),ns=ns(),ym=ym());print('SymPy',S.__version__,results,'TOTAL',sum(results.values()),'PASS')
