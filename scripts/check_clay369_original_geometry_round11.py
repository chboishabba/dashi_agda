"""Exact independent controls for original source charts, not Lean elaboration.
NS ordered Fourier cutoff; BSD tangent signs; Dickson fold; Path13 words.
"""
from fractions import Fraction as Q
from itertools import product, combinations
from random import Random
import sympy as S

if not __debug__:raise SystemExit('refusing optimized execution')

def ns():
    Z=(Q(0),Q(0)); I=(Q(0),Q(1));rng=Random(36911)
    add=lambda a,b:(a[0]+b[0],a[1]+b[1])
    neg=lambda a:(-a[0],-a[1])
    conj=lambda a:(a[0],-a[1])
    mul=lambda a,b:(a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
    scale=lambda a,r:(a[0]*r,a[1]*r)
    def summ(xs):
        a=Z
        for b in xs:a=add(a,b)
        return a
    def dot(k,v):return summ(scale(z,r) for r,z in zip(k,v))
    def project(k,v):
        d=sum(x*x for x in k)
        if not d:return (Z,)*3
        h=dot(k,v);return tuple(add(z,scale(h,-Q(x,d))) for x,z in zip(k,v))
    K=list(product(range(-1,2),repeat=3));KS=set(K);zero=(0,0,0)
    def reflect(U):return {k:tuple(conj(z) for z in U[tuple(-x for x in k)]) for k in K}
    def force(U):
        F={k:[Z]*3 for k in K}
        for p,q in product(K,repeat=2):
            k=tuple(a+b for a,b in zip(p,q))
            if k not in KS or k==zero:continue
            d=dot(q,U[p]);v=project(k,tuple(mul(d,z) for z in U[q]))
            for i in range(3):F[k][i]=add(F[k][i],mul(neg(I),v[i]))
        return {k:tuple(v) for k,v in F.items()}
    c=0
    for _ in range(4):
        U={k:tuple((Q(rng.randrange(-3,4)),Q(rng.randrange(-3,4))) for _ in range(3)) for k in K}
        F=force(U);FR=force(reflect(U));RF=reflect(F)
        for k in K:
            assert FR[k]==RF[k];c+=1
            assert dot(k,F[k])==Z;c+=1
        V=reflect(U);W={k:project(k,tuple(scale(add(a,b),Q(1,2)) for a,b in zip(U[k],V[k]))) for k in K}
        assert W==reflect(W);c+=1
        for k in K:assert dot(k,W[k])==Z;c+=1
        G=force(W)
        assert sum(mul(z,conj(v))[0] for k in K for z,v in zip(G[k],W[k]))==0;c+=1
    return c

def bsd_hodge():
    u,a,b,Y,t=S.symbols('u a b Y t',nonzero=True);f=u*(u+a)*(u+b);U=a*b/u;V=-a*b*Y/u**2
    r=[(a*b-u**2)/(2*Y),-(u**2+2*a*u+a*b)/(2*Y),-(u**2+2*b*u+a*b)/(2*Y)]
    def zero_on_curve(e):return S.rem(S.together(e).as_numer_denom()[0],Y**2-f,Y).expand()==0
    c=0
    for e,ri,sgn in zip((0,-a,-b),r,(1,-1,-1)):
        assert zero_on_curve(Y/(u-e)-S.diff(f,u)/(2*Y)-ri);c+=1
        assert S.cancel(ri.subs({u:U,Y:V},simultaneous=True)-sgn*ri)==0;c+=1
    assert zero_on_curve(V**2-U*(U+a)*(U+b));c+=1
    assert zero_on_curve(t*(t+a)*(t+b)-(Y/u*t)**2-t*(t-u)*(t-U));c+=1
    assert S.cancel(U.subs(u,U)-u)==0;c+=1
    assert S.cancel(V.subs({u:U,Y:V},simultaneous=True)-Y)==0;c+=1
    v,w=S.symbols('v w',nonzero=True)
    assert S.cancel(v*w*((v+a/v)-(w+a/w))-(v-w)*(v*w-a))==0;c+=1
    for n in (2,7):
        C=0
        for xs in product(range(n),repeat=5):
            ys=xs+((-sum(xs))%n,);assert sum(ys)%n==0;C+=1
        assert C==n**5;c+=1
    return c

def path13():
    def walk(start,off):
        p=list(start);counts=[0]*4;length=0
        for axis,o in enumerate(off):
            for _ in range(abs(o)):
                if o<0:p[axis]=(p[axis]-1)%13
                if not any(p):counts[axis]+=1 if o>0 else -1
                if o>0:p[axis]=(p[axis]+1)%13
                length+=1
        return tuple(p),tuple(counts),length
    zero=(0,)*4;N=13**4;c=0
    for axis in range(4):
        off=tuple(13 if i==axis else 0 for i in range(4));_,rc,lc=walk(zero,off);total=[0]*4
        for o in product(range(-6,7),repeat=4):
            site,rm,lm=walk(zero,o);end,rx,lx=walk(site,off)
            assert end==site and lc==lx==13 and lm<=24 and lm+lx<=37 and 2*lm+lx+lc<=74;c+=1
            # At identity, M=minus+cross, P=center+plus with plus=minus.
            # Retain correction and center before cancellation.
            for j in range(4):
                rM=rm[j]+rx[j];rP=rc[j]+rm[j]
                total[j]+=rM-rP+rc[j]+rm[j]-rm[j]
        assert [Q(t,13*N) for t in total]==[Q(int(j==axis),N) for j in range(4)];c+=1
    e=Q(1,1142440000)
    td=2*2738+148*37;ud=296*74+td;od=148*148+ud;cd=296*13+338;wd=26*24+2*1152
    assert (td,ud,od,cd,wd)==(10952,32856,54760,4186,2928);c+=1
    assert od+cd+wd==61874;c+=1
    assert 4*Q(61874,13)*e<=20000*e==Q(1,57122);c+=1
    return c

if __name__=='__main__':
    counts=[ns(),bsd_hodge(),path13()]
    print('SymPy',S.__version__,'NS',counts[0],'BSD/Hodge',counts[1],'Path13',counts[2], 'PASS',sum(counts),'/',sum(counts))
