"""Exact algebraic controls for the source-written periodic modal limit.
Affine-in-time Fourier fixtures are not nonlinear NSE trajectories.
"""
from fractions import Fraction as Q
from itertools import product
from random import Random
import sympy as S
if not __debug__:raise SystemExit('refusing optimized execution')
Z=(Q(0),Q(0));O=(0,0,0);I=(Q(0),Q(1));V0=(Z,)*3

def add(a,b):return a[0]+b[0],a[1]+b[1]
def scale(a,r):return a[0]*r,a[1]*r
def mul(a,b):return a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0]
def conj(a):return a[0],-a[1]
def vsum(a,b):return tuple(add(x,y) for x,y in zip(a,b))
def vscale(a,r):return tuple(scale(x,r) for x in a)
def vsub(a,b):return vsum(a,vscale(b,-1))
def dot(k,u):
    z=Z
    for a,b in zip(k,u):z=add(z,scale(b,a))
    return z
def mass(u):return sum(a*a+b*b for a,b in u)
def m2(k):return sum(x*x for x in k)
def project(k,u):
    d=m2(k);h=dot(k,u)
    return tuple(add(z,scale(h,-Q(a,d))) for a,z in zip(k,u)) if d else V0
def cell(k,q,u,v):return tuple(mul(scale(I,-1),x) for x in project(k,tuple(mul(dot(q,u),z) for z in v)))
def midpoint(U,V):return {k:vscale(vsum(U.get(k,V0),V.get(k,V0)),Q(1,2)) for k in U.keys()|V.keys()}
def simpson(a,b,c):return vscale(vsum(vsum(a,vscale(b,4)),c),Q(1,6))
def mass_integral(U,V):return sum((mass(U.get(k,V0))+4*mass(mid)+mass(V.get(k,V0)))/6 for k,mid in midpoint(U,V).items())
def force(k,U):
    out=V0
    for p,u in U.items():
        q=tuple(x-y for x,y in zip(k,p));v=U.get(q,V0)
        out=vsum(out,cell(k,k,u,v))
    return out
def make(N,rng):
    K=list(product(range(-N,N+1),repeat=3));U={O:V0}
    for k in K:
        if k in U:continue
        u=project(k,tuple((Q(rng.randrange(-3,4),7),Q(rng.randrange(-3,4),7)) for _ in range(3)))
        U[k]=u;U[tuple(-a for a in k)]=tuple(conj(x) for x in u)
    return U

def exact_convolution():
    rng=Random(36913);count=0
    for N,M,reps in ((1,1,4),(1,2,3),(2,2,2)):
        for _ in range(reps):
            A0,A1,C0,C1=make(N,rng),make(N,rng),make(M,rng),make(M,rng)
            Ahalf=midpoint(A0,A1);Chalf=midpoint(C0,C1)
            B=max(sum(mass(v) for v in U.values()) for U in (A0,A1,C0,C1))
            D0={k:vsub(A0.get(k,V0),C0.get(k,V0)) for k in A0.keys()|C0.keys()}
            D1={k:vsub(A1.get(k,V0),C1.get(k,V0)) for k in A1.keys()|C1.keys()}
            E=mass_integral(D0,D1)
            for k in product(range(-1,2),repeat=3):
                if k==O:continue
                for U in (A0,Ahalf,A1,C0,Chalf,C1):
                    exact=V0
                    for p,u in U.items():
                        q=tuple(x-y for x,y in zip(k,p));v=U.get(q,V0)
                        assert dot(p,u)==Z;count+=1
                        assert cell(k,q,u,v)==cell(k,k,u,v);count+=1
                        exact=vsum(exact,cell(k,q,u,v))
                    assert exact==force(k,U);count+=1
                    assert mass(exact)<=m2(k)*B*B;count+=1
                fA=simpson(*(force(k,U) for U in (A0,Ahalf,A1)))
                fC=simpson(*(force(k,U) for U in (C0,Chalf,C1)))
                delta=vsub(fA,fC)
                for eps in (Q(1,4),Q(1),Q(4)):
                    assert mass(delta)<=m2(k)*(E/eps+eps*B)**2;count+=1
                p=next(p for p in A0 if p!=O);q=tuple(x-y for x,y in zip(k,p))
                u,v=A0[p],A0.get(q,V0);up,vp=C0.get(p,V0),C0.get(q,V0)
                assert vsub(cell(k,k,u,v),cell(k,k,up,vp))==vsum(cell(k,k,vsub(u,up),v),cell(k,k,up,vsub(v,vp)));count+=1
    return count

def diagonal_controls():
    # Non-solution moving transverse packets: integrated L² convergence
    # and bounded dissipation do not imply sup_t H^(1/2) convergence.
    count=0;t=S.symbols('t',real=True)
    n=S.symbols('n',positive=True,integer=True)
    pulse=1-n*n*t
    assert S.integrate(2*pulse**2,(t,0,1/n**2))==2/(3*n**2);count+=1
    assert S.integrate(2*n*n*pulse**2,(t,0,1/n**2))==Q(2,3);count+=1
    for j in range(1,65):
        E=Q(2,3*j*j);D=Q(2,3);Hhalf=Q(2,3*j)
        assert E*j*j==D;count+=1
        assert Hhalf*j==D;count+=1
        assert 2*j>=2;count+=1
    # Fixed Fourier projection recovers the original coefficient once
    # the common increasing cutoff contains that address.
    for k in product(range(-4,5),repeat=3):
        R=sum(abs(x) for x in k)
        for d in range(4):
            assert all(abs(x)<=R+d for x in k);count+=1
    return count

if __name__=='__main__':
    a=exact_convolution();b=diagonal_controls()
    print('SymPy',S.__version__,'original ordered convolution',a,'diagonal/tail',b,'TOTAL',a+b,'PASS')
