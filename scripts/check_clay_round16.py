"""Exact cross-Clay controls; no native proof or unrestricted complexity receipt.
Finite split elliptic groups test actual chord/tangent addition, not E(Q) rank.
NS pressure and weighted errors are algebraic fixtures, not PDE solutions.
Hodge is the actual folded chart polynomial identity, not a Chow pairing.
YM unit quaternions are rational fixtures, not the selected CMP102 word.
"""
from fractions import Fraction as Q
from itertools import product
from random import Random
from math import prod
import sympy as S
if not __debug__:raise SystemExit('refusing optimized execution')

def bsd():
    count=0
    for p in (5,7,11,13,17,19,23,29,31,37,41,43,47):
        pts=[None]+[(x,y) for x in range(p) for y in range(p) if (y*y-x*x*x+x)%p==0]
        def neg(a):return None if a is None else (a[0],-a[1]%p)
        def add(a,b):
            if a is None:return b
            if b is None:return a
            x,y=a;z,w=b
            if x==z and (y+w)%p==0:return None
            m=((3*x*x-1)*pow(2*y,-1,p) if x==z else (w-y)*pow(z-x,-1,p))%p
            X=(m*m-x-z)%p;return X,(m*(x-X)-y)%p
        D={a:add(a,a) for a in pts};T={a for a in pts if D[a] is None}
        assert T=={None,(0,0),(1,0),(p-1,0)};count+=1
        for a in pts:
            assert {add(a,t) for t in T}=={b for b in pts if D[b]==D[a]};count+=1
            for b in pts:
                assert (D[a]==D[b])==(add(a,neg(b)) in T);count+=1
        assert len(set(D.values()))*4==len(pts);count+=1
    r,s,t,x=S.symbols('r s t x');e0=x-r*r;e1=x-s*s;e2=x-t*t
    X=x+r*s+s*t+t*r;Y=-(r+s)*(s+t)*(t+r)
    Xp=X.subs({s:-s,t:-t},simultaneous=True);Yp=Y.subs({s:-s,t:-t},simultaneous=True)
    A=(e0-e1)*(e0-e2)
    assert S.cancel((Xp-e0)-A/(X-e0))==0;count+=1
    assert S.cancel(Yp+A*Y/(X-e0)**2)==0;count+=1
    assert S.expand(X-Xp-2*r*(s+t))==0;count+=1
    return count

def hodge():
    a,x,v=S.symbols('a x v')
    assert S.expand((v*v-a)**2-v*v*(x*x-4*a)-(v*v+x*v+a)*(v*v-x*v+a))==0
    count=1;rng=Random(36916)
    for _ in range(128):
        A=[Q(rng.randrange(1,12),rng.randrange(1,9)) for _ in range(6)]
        V=[Q(rng.randrange(1,12),rng.randrange(1,9)) for _ in range(6)]
        X=[v+a/v for a,v in zip(A,V)];eta=prod(V);delta=Q(rng.randrange(-3,4))
        den=eta*delta*prod(a*v*(v*v-a) for a,v in zip(A,V))
        base=eta**6*delta**2*prod(a*a*(x*x-4*a) for a,x in zip(A,X))
        assert den**2==base;count+=1
        assert (den==0)==(base==0);count+=1
    return count

def ns():
    rng=Random(316);count=0;I=S.I
    for _ in range(128):
        k=S.Matrix([rng.randrange(-4,5) for _ in range(3)])
        if k.dot(k)==0:k[0]=1
        u,v,z=[S.Matrix([rng.randrange(-3,4)+I*rng.randrange(-3,4) for _ in range(3)]) for _ in range(3)]
        m=k.dot(k);raw=I*k.dot(u)*v;P=(raw-k*k.dot(raw)/m).expand()
        pressure=-k.dot(u)*k.dot(v)/m
        assert (-P+raw+I*k*pressure).expand()==S.zeros(3,1);count+=1
        z=(z-k*k.dot(z)/m).expand()
        assert S.expand((-I*k*pressure).dot(z.conjugate()))==0;count+=1
    for n in range(1,257):
        # concentrated moving-mode error, e=n^-2, squared-radius moment=1
        E=Q(1,n*n);D=1;H=n*E
        assert H*H<=E*D;count+=1
        for a in (Q(1,10),Q(1,2),Q(2)):
            assert H<=a*D+E/(4*a);count+=1
    return count

def ym():
    def dot(a,b):return sum(x*y for x,y in zip(a,b))
    def sub(a,b):return tuple(x-y for x,y in zip(a,b))
    def mul(a,b):
        x,u,v,w=a;y,i,j,k=b
        return (x*y-u*i-v*j-w*k,x*i+u*y+v*k-w*j,x*j-u*k+v*y+w*i,x*k+u*j-v*i+w*y)
    def star(a):return (a[0],*(-x for x in a[1:]))
    rng=Random(7416);count=0;one=(Q(1),0,0,0)
    for _ in range(256):
        v=[Q(rng.randrange(-8,9),10) for _ in range(3)];r=dot(v,v);q=((1-r)/(1+r),*(2*x/(1+r) for x in v))
        H=tuple(Q(rng.randrange(-8,9),7) for _ in range(4));C=mul(mul(q,H),star(q));chord=dot(sub(q,one),sub(q,one))
        assert dot(q,q)==1;count+=1
        assert chord==2-2*q[0];count+=1
        assert dot(C,C)==dot(H,H);count+=1
        assert dot(sub(C,H),sub(C,H))<=4*chord*dot(H,H);count+=1
    return count

if __name__=='__main__':
    r=dict(bsd=bsd(),hodge=hodge(),ns=ns(),ym=ym());print('SymPy',S.__version__,r,'TOTAL',sum(r.values()),'PASS')
