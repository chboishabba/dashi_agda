"""Independent exact Gaussian-rational fixed-mode force controls."""
from fractions import Fraction as Q
from itertools import product
from random import Random
if not __debug__:raise SystemExit('refusing optimized execution')
Z=(Q(0),Q(0));I=(Q(0),Q(1));O=(0,0,0)
def add(a,b):return a[0]+b[0],a[1]+b[1]
def scale(a,r):return a[0]*r,a[1]*r
def mul(a,b):return a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0]
def conj(a):return a[0],-a[1]
def dot(k,u):
    z=Z
    for a,b in zip(k,u):z=add(z,scale(b,a))
    return z
def mass(u):return sum(a*a+b*b for a,b in u)
def project(k,u):
    d=sum(a*a for a in k);h=dot(k,u)
    return tuple(add(z,scale(h,-Q(a,d))) for a,z in zip(k,u)) if d else (Z,)*3

def main():
    rng=Random(36912);checks=0
    for N,reps in ((1,6),(2,3),(3,1)):
        K=list(product(range(-N,N+1),repeat=3));KS=set(K)
        for _ in range(reps):
            U={O:(Z,)*3}
            for k in K:
                if k not in U:
                    U[k]=project(k,tuple((Q(rng.randrange(-3,4),7),Q(rng.randrange(-3,4),7)) for i in range(3)))
                    U[tuple(-a for a in k)]=tuple(conj(v) for v in U[k])
            E=sum(mass(u) for u in U.values())
            for k in K:
                if k==O:continue
                r2=sum(a*a for a in k);pairs=[];F=[Z]*3
                for p in K:
                    q=tuple(a-b for a,b in zip(k,p))
                    if q not in KS:continue
                    pairs.append((p,q))
                    a=dot(q,U[p]);assert a==dot(k,U[p]);checks+=1
                    cell=project(k,tuple(mul(a,v) for v in U[q]))
                    assert mass(cell)<=r2*mass(U[p])*mass(U[q]);checks+=1
                    for i,z in enumerate(cell):F[i]=add(F[i],mul(scale(I,-1),z))
                assert len({p for p,q in pairs})==len(pairs)==len({q for p,q in pairs});checks+=1
                assert sum(mass(U[p]) for p,q in pairs)<=E;checks+=1
                assert sum(mass(U[q]) for p,q in pairs)<=E;checks+=1
                assert mass(F)<=r2*E*E;checks+=1
                for z in F:assert mass([z])<=r2*E*E;checks+=1
    print(f'{checks}/{checks} fixed-output exact controls PASS')
if __name__=='__main__':main()
