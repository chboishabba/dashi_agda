#!/usr/bin/env python3
"""BR187 full hydrogenic n=2 projected Coulomb; BR188 scalar CK majorant.
Finite shell and conditional scalar bound, not full atom or PDE acceptance.
"""
import sympy as s
from itertools import combinations
from functools import lru_cache
from sympy.physics.wigner import gaunt
Q=s.Rational
r,t=s.symbols('r t',positive=True)
R=[(2-r)*s.exp(-r/2)/(2*s.sqrt(2)),r*s.exp(-r/2)/(2*s.sqrt(6))]
@lru_cache(None)
def radial(a,c,b,d,k):
    f=r*r*R[a]*R[c];g=r*r*R[b]*R[d]
    def half(f,g):
        return s.integrate(s.expand(f/r**(k+1)*s.integrate((g*r**k).subs(r,t),(t,0,r))),(r,0,s.oo))
    return s.simplify(half(f,g)+half(g,f))

def atomic():
    from check_hopf369_br172_174_joint import atomic as one
    from check_hopf369_br154_156_atomic import coulomb
    from check_hopf369_br186_interacting_shell import wedge,lift,eq
    H,J,U,params=one()
    Vp,_,_,pp=coulomb()
    for args,val in [((0,0,0,0,0),77),((0,0,1,1,0),83),((0,1,0,1,1),45),((1,1,1,1,0),93),((1,1,1,1,2),45)]:
        assert radial(*args)==Q(val,512)
    modes=[(l,m,spin) for l in (0,1) for m in range(-l,l+1) for spin in (-1,1)]
    pairs=list(combinations(range(8),2))
    @lru_cache(None)
    def eri(a,b,c,d):
        la,ma,sa=modes[a];lb,mb,sb=modes[b];lc,mc,sc=modes[c];ld,md,sd=modes[d]
        if sa!=sc or sb!=sd:return s.S.Zero
        out=0
        for k in range(3):
            if not(abs(la-lc)<=k<=la+lc and abs(lb-ld)<=k<=lb+ld):continue
            if (la+lc+k)%2 or (lb+ld+k)%2:continue
            for q in range(-k,k+1):
                g=gaunt(la,k,lc,-ma,-q,mc)*gaunt(lb,k,ld,-mb,q,md)
                if g:out+=4*s.pi*(-s.S.One)**(ma+mb+q)*g*radial(la,lc,lb,ld,k)/(2*k+1)
        return s.simplify(out)
    V=s.Matrix(28,28,lambda i,j:eri(*pairs[i],*pairs[j])-eri(*pairs[i],*pairs[j][::-1]))
    eq(V,V.T)
    ids=[i for i,(a,b) in enumerate(pairs) if a>=2 and b>=2]
    eq(V[ids,ids],Vp)
    orb={-1:s.Matrix([1,-s.I,0])/s.sqrt(2),0:s.Matrix([0,0,1]),1:-s.Matrix([1,s.I,0])/s.sqrt(2)}
    E=s.zeros(8)
    for j,(l,m,spin) in enumerate(modes):
        z=0 if spin==1 else 1
        if l==0:E[z,j]=1
        else:
            for i in range(3):E[2+2*i+z,j]=orb[m][i]
    eq(E.H*E,s.eye(8))
    W=wedge(E,pairs,pairs)
    C=(W*V*W.H).applyfunc(s.simplify)
    H2=lift(H,pairs)+C; J2=lift(J,pairs); U2=wedge(U,pairs,pairs)
    eq(H2,H2.H);eq(H2*J2,J2*H2);eq(U2*H2.conjugate()*U2.H,H2)
    print('BR187 full n=2 Coulomb eigenvalues',V.eigenvals())
    print('PASS BR187 actual complete projected n=2 Coulomb and BR172 interaction')

def lifespan():
    # P0V implicit scalar majorant P=(1-z/rho)w-A*w^2/2-c*t.
    rho,eta,c,n=s.symbols('rho eta c n',positive=True)
    A=n*(3/rho+1/eta)
    z=rho/2; w=1/(4*A); t0=Q(3,32)/(A*c)
    assert s.simplify((1-z/rho)*w-A*w*w/2-c*t0)==0
    assert s.simplify(1-z/rho-A*w)==Q(1,4)
    print('PASS BR188 conditional scalar CK majorant at half radius: t0=3/(32*A*c), w<=1/(4*A)')
if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--part',required=True,choices=['atomic','lifespan'])
    globals()[p.parse_args().part]()
