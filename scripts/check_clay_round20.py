"""Independent Section 20 controls; no native proof acceptance."""
from collections import Counter
from fractions import Fraction as F
from itertools import product
from random import Random
import sympy as s
if not __debug__: raise SystemExit('assertions required')
C=Counter(); g=Random(36920)
def check(lane, cond):
    assert cond, lane
    C[lane]+=1

# NS: actual signed cube, full ordered force, zero output and reflection.
K=list(product((-1,0,1),repeat=3)); Z=(0,0); zero=(Z,)*3
neg=lambda k:tuple(-a for a in k)
add=lambda a,b:(a[0]+b[0],a[1]+b[1])
mul=lambda a,b:(a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
scale=lambda a,b:(a*b[0],a*b[1])
conj=lambda a:(a[0],-a[1])
def dot(k,v):
    return tuple(sum(k[i]*v[i][j] for i in range(3)) for j in range(2))
def force(U):
    ans={k:zero for k in K}
    for p,q in product(K,repeat=2):
        k=tuple(a+b for a,b in zip(p,q))
        if k not in ans or k==(0,0,0): continue
        w=tuple(mul(dot(q,U[p]),z) for z in U[q]); d=dot(k,w); m=sum(a*a for a in k)
        v=tuple(mul((0,-1),add(z,scale(-F(a,m),d))) for a,z in zip(k,w))
        ans[k]=tuple(add(a,b) for a,b in zip(ans[k],v))
    return ans
def reflect(U): return {k:tuple(conj(z) for z in U[neg(k)]) for k in K}
for _ in range(16):
    U={k:tuple((g.randrange(-2,3),g.randrange(-2,3)) for i in range(3)) for k in K}
    A=force(U); B=force(reflect(U)); D=reflect(A)
    for k in K:
        check('NS',B[k]==D[k]); check('NS',dot(k,A[k])==Z)
    check('NS',A[(0,0,0)]==zero)
    # The actual reflected viscous term also commutes.
    for k in K:
        a=-sum(i*i for i in k)
        check('NS',tuple(scale(a,z) for z in reflect(U)[k])==tuple(conj(scale(a,z)) for z in U[neg(k)]))

# Hodge: actual homogeneous substitution over possibly nonreduced rings.
for mod in (4,8,9,12,16,25,27,32):
    for _ in range(32):
        vals=(1,*(g.randrange(mod) for i in range(4)))
        terms=[(g.randrange(mod),tuple(g.randrange(4) for i in vals)) for j in range(20)]
        mapped=[0]*16; components=[0]*16
        for c,e in terms:
            poly=[c]
            for v,n in zip(vals,e):
                for j in range(n): poly=[0]+[(a*v)%mod for a in poly]
            for j,a in enumerate(poly): mapped[j]=(mapped[j]+a)%mod
            components[sum(e)]=(components[sum(e)]+c*s.prod(pow(v,n,mod) for v,n in zip(vals,e)))%mod
        check('Hodge',mapped==components)
        check('Hodge',sum(mapped)%mod==sum(c*s.prod(pow(v,n,mod) for v,n in zip(vals,e)) for c,e in terms)%mod)
        check('Hodge',(not any(mapped))==(not any(components)))

# BSD: Frobenius of actual reverse halves over F_p^2, not arbitrary signs.
for p in (5,7,11,13,17,19,23):
    d=next(i for i in range(2,p) if pow(i,(p-1)//2,p)==p-1)
    fadd=lambda a,b:((a[0]+b[0])%p,(a[1]+b[1])%p)
    fneg=lambda a:((-a[0])%p,(-a[1])%p)
    fmul=lambda a,b:((a[0]*b[0]+d*a[1]*b[1])%p,(a[0]*b[1]+a[1]*b[0])%p)
    frob=lambda a:(a[0],-a[1]%p)
    def fpow(a,n):
        r=(1,0)
        while n:
            if n&1:r=fmul(r,a)
            a=fmul(a,a);n//=2
        return r
    def sub(a,b):return fadd(a,fneg(b))
    def div(a,b):
        assert b!=Z
        return fmul(a,fpow(b,p*p-2))
    def padd(P,Q):
        if P is None:return Q
        if Q is None:return P
        x,y=P;u,v=Q
        if x==u and fadd(y,v)==Z:return None
        m=div(sub(fmul((3,0),fmul(x,x)),(1,0)),fmul((2,0),y)) if x==u else div(sub(v,y),sub(u,x))
        z=sub(sub(fmul(m,m),x),u)
        return z,sub(fmul(m,sub(x,z)),y)
    roots=(0,1,p-1); allf=list(product(range(p),repeat=2))
    for x in range(p):
        if x in roots:continue
        rs=[[a for a in allf if fmul(a,a)==((x-e)%p,0)] for e in roots]
        for a,b,c in product(*rs):
            y=fneg(fmul(fmul(a,b),c))
            if y[1]:continue
            def half(a,b,c):
                X=fadd((x,0),fadd(fadd(fmul(a,b),fmul(b,c)),fmul(c,a)))
                Y=fneg(fmul(fmul(fadd(a,b),fadd(b,c)),fadd(c,a)))
                return X,Y
            Q=half(a,b,c); R=half(frob(a),frob(b),frob(c))
            check('BSD',padd(Q,Q)==((x,0),y))
            check('BSD',R==tuple(frob(z) for z in Q))
            signs=tuple(frob(z)==z for z in (a,b,c))
            want=None if all(signs) else ((roots[signs.index(True)],0),Z)
            check('BSD',padd(R,(Q[0],fneg(Q[1])))==want)

# YM: exact unit quaternion signed word body recursion and reopen.
def qm(a,b):
    w,x,y,z=a;t,u,v,h=b
    return (w*t-x*u-y*v-z*h,w*u+x*t+y*h-z*v,w*v-x*h+y*t+z*u,w*h+x*v-y*u+z*t)
def qs(a):return (a[0],*(-x for x in a[1:]))
def qa(a,b):return tuple(x+y for x,y in zip(a,b))
def qn(a):return sum(x*x for x in a)
def unit():
    x,y,z=(F(g.randrange(-4,5),3) for i in range(3)); d=1+x*x+y*y+z*z
    return ((2-d)/d,2*x/d,2*y/d,2*z/d)
for _ in range(128):
    V=(1,0,0,0); D=(0,0,0,0); B=D
    for i in range(g.randrange(1,8)):
        q=unit(); h=(0,*(F(g.randrange(-4,5),3) for j in range(3))); negative=g.randrange(2)
        b=qs(q) if negative else q
        db=tuple(-x for x in qm(h,qs(q))) if negative else qm(q,h)
        body=qm(qs(b),db)
        check('YM',body==(tuple(-x for x in qm(qm(q,h),qs(q))) if negative else h))
        B=qa(qm(qm(qs(V),body),V),B); D,V=qa(qm(db,V),qm(b,D)),qm(b,V)
        check('YM',B==qm(qs(V),D));check('YM',qm(V,B)==D);check('YM',qn(B)==qn(D))

# PNP: reachable distinct endpoint rivals and disjoint windows on one run.
for _ in range(128):
    widths=[g.randrange(1,7) for j in range(g.randrange(1,9))]; T=sum(widths); a=0; events=[]
    x=[g.randrange(2) for j in range(T)]
    def state(z,t):return sum(z[:t])%2
    for L in widths:
        j=g.randrange(a,a+L); y=x.copy();y[j]^=1
        check('PNP',state(x,a)==state(y,a) and state(x,a+L)!=state(y,a+L))
        k=next(t for t in range(a,a+L) if state(x,t+1)!=state(y,t+1))
        check('PNP',a<=k<a+L and state(x,k)==state(y,k) and x[k]!=y[k])
        events.append(k);a+=L
    check('PNP',len(set(events))==len(widths)<=T)
print(dict(C),'TOTAL',sum(C.values()),'PASS')
