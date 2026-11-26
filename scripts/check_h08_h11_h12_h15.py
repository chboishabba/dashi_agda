#!/usr/bin/env python3
"""Selected source contracts: actual finite fields, renderer, sparse tower, strip MAX-CUT."""
from itertools import product
from fractions import Fraction as F
from dataclasses import dataclass
import numpy as np
import sympy as s

def need(ok, label):
    if not bool(ok): raise RuntimeError(label)

class Field:
    def __init__(self, coeff):
        self.n=len(coeff); self.coeff=coeff
        self.size=3**self.n
        self.zero=(0,)*self.n; self.one=(1,)+(0,)*(self.n-1)
    def add(self,a,b): return tuple((x+y)%3 for x,y in zip(a,b))
    def mul(self,a,b):
        n=self.n; c=[0]*(2*n-1)
        for i,x in enumerate(a):
            for j,y in enumerate(b): c[i+j]+=x*y
        for k in range(2*n-2,n-1,-1):
            for i,x in enumerate(self.coeff): c[k-n+i]-=c[k]*x
        return tuple(x%3 for x in c[:n])
    def pow(self,a,k):
        r=self.one
        while k:
            if k&1:r=self.mul(r,a)
            a=self.mul(a,a);k//=2
        return r
    def primitive(self):
        factors=s.factorint(self.size-1)
        for a in product(range(3),repeat=self.n):
            if a!=self.zero and all(self.pow(a,(self.size-1)//p)!=self.one for p in factors):return a
        raise RuntimeError('primitive')
    def orbit(self,g):
        a=self.one; out=[]
        for _ in range(self.size-1):out.append(a);a=self.mul(a,g)
        need(a==self.one and len(set(out))==self.size-1,'primitive orbit')
        return out
    def cubic_root(self,orbit):
        for a in orbit[::(self.size-1)//26]:
            if self.pow(a,3)==self.add(a,self.one):return a
        raise RuntimeError('cubic root')
    def embed(self,a,r):
        v=self.zero
        for c in reversed(a):v=self.add(self.mul(v,r),(c,)+(0,)*(self.n-1))
        return v

def fields():
    # Original Route C x^9+x^4-1 and original GF729 x^6+x^5+x^4+1.
    f=Field((2,0,0,0,1,0,0,0,0)); g=Field((1,0,0,0,1,1)); h=Field((2,2,0))
    x=s.symbols('x')
    for k in (f,g,h):need(s.Poly(x**k.n+sum(c*x**i for i,c in enumerate(k.coeff)),x,modulus=3).is_irreducible,'irreducible')
    orb=f.orbit(f.primitive()); delta=(0,1,0,1,1,0); og=g.orbit(delta)
    rf=f.cubic_root(orb); rg=g.cubic_root(og); hs=list(product(range(3),repeat=3))
    ef={a:f.embed(a,rf) for a in hs}; eg={a:g.embed(a,rg) for a in hs}
    need(len(set(ef.values()))==len(set(eg.values()))==27,'embedded GF27')
    for a,b in product(hs,repeat=2):
        for k,e in ((f,ef),(g,eg)):
            need(e[h.add(a,b)]==k.add(e[a],e[b]) and e[h.mul(a,b)]==k.mul(e[a],e[b]),'subfield homomorphism')
    log={a:i for i,a in enumerate(orb)}; logg={a:i for i,a in enumerate(og)}
    # Actual Frobenius on original field (all points), relative trace/norm.
    fixes=[]; roots=(rf,rg)
    for k,orbit,logs,e in ((f,orb,log,ef),(g,og,logg,eg)):
        m=k.size-1; sub=set(e.values()); fixed={k.zero}; trace_zero=0; norm_zero=0
        for i,a in enumerate(orbit):
            b=k.pow(a,27); need(b==orbit[(27*i)%m],'Frob^3 actual')
            if b==a:fixed.add(a)
            tr=k.zero; z=a
            for j in range(k.n//3):tr=k.add(tr,z);z=orbit[(logs[z]*27)%m]
            norm=orbit[(i*(m//26))%m]
            need(tr in sub and norm in sub,'relative trace/norm')
            trace_zero+=tr==k.zero; norm_zero+=norm==k.zero
        need(fixed==sub and norm_zero==0,'fixed field')
        fixes.append((k.n,len(fixed),trace_zero+1))
        need(trace_zero+1==3**(k.n-3),'trace kernel rank')
    # Literal original ATLAS compression T, field multiplication M, Q.
    T=s.Matrix([[-1,-1,0,1,1,-1],[0,0,0,1,1,-1],[-1,1,0,0,0,0],[1,-1,0,-1,-1,-1],[0,0,1,1,1,-1],[0,0,1,-1,1,1]])
    M=s.Matrix([[0,0,-1,0,1,1],[1,0,0,-1,0,1],[0,1,0,0,-1,0],[1,0,1,0,0,-1],[1,1,-1,1,1,1],[0,1,0,-1,-1,-1]])
    Q=s.Matrix([[1,1,0,1,0,0],[0,-1,0,1,-1,-1],[0,0,1,1,0,1],[0,1,1,-1,0,-1],[0,-1,-1,0,-1,-1],[0,-1,-1,-1,-1,-1]])
    need(int(Q.det())%3==2 and all(int(v)%3==0 for v in Q*T-M*Q),'literal Q T=M Q')
    for i in range(6):need(tuple(int(M[j,i])%3 for j in range(6))==g.mul(delta,tuple(int(j==i) for j in range(6))),'actual multiplication matrix')
    # Transport source compression power to common GF27. No GF729 into GF19683.
    need(set(og[::28])==set(eg.values())-{g.zero},'delta^28 subfield orbit')
    print('H08 fields',fixes,'shared roots',roots,'GF27 pair laws',2*27**2,'source Q T=M Q, delta^28 order26',flush=True)

def pixel(x):
    c,m,y,k,a=x
    return (a*(1-m)*(1-k),a*(1-y)*(1-k),a*(1-c)*(1-k),1-a)
def compose(a,b):return tuple(a[i]+a[3]*b[i] for i in range(3))+(a[3]*b[3],)
def moments(xs):
    return tuple(sum(a*v for c,m,y,k,a in xs for v in [fn(c,m,y,k)]) for fn in (lambda c,m,y,k:1,lambda c,m,y,k:m,lambda c,m,y,k:y,lambda c,m,y,k:c,lambda c,m,y,k:k,lambda c,m,y,k:m*k,lambda c,m,y,k:y*k,lambda c,m,y,k:c*k))
def read_mom(v):
    a,m,y,c,k,mk,yk,ck=v;return (a-m-k+mk,a-y-k+yk,a-c-k+ck)
def renderer():
    bit=list(product((0,1),repeat=5)); checks=0
    for c,m,y,k,a in bit:need(pixel((c,m,y,k,a))[:3]==tuple(a*int(not v)*int(not k) for v in (m,y,c)),'literal bit renderer')
    for p,q in product(bit,repeat=2):
        need(read_mom(moments([p,q]))==tuple(pixel(p)[i]+pixel(q)[i] for i in range(3)),'additive moment')
        checks+=1
    half=F(1,2); colors=[pixel(x) for x in product((0,half,1),repeat=5)]
    for i,p in enumerate(colors):
        q=colors[(i*7+3)%len(colors)];r=colors[(i*11+1)%len(colors)]
        need(compose(compose(p,q),r)==compose(p,compose(q,r)),'ordered composition')
    need(compose((half,0,0,half),(0,half,0,half))!=compose((0,half,0,half),(half,0,0,half)),'order negative control')
    need(pixel((0,0,0,0,0))==pixel((1,1,1,1,0)),'hidden transparent colour')
    print('H11 bit states',len(bit),'additive pairs',checks,'rational associativity',len(colors),flush=True)

# Original I0=unit, I(n+1)=I(n)->Fin9. Canonical finite support over
# zero baseline; any default allowed at levels >=3 if exceptions < half domain.
def capped_sites(level,cap):
    v=1
    for _ in range(level):
        r=1
        for _ in range(v):
            r*=9
            if r>=cap:break
        v=min(r,cap)
    return v
@dataclass(frozen=True)
class Node:
    level:int; default:int; overrides:tuple
UNIT=Node(0,0,())
def make(level,default,items):
    need(level>0 and 0<=default<9,'level/digit')
    d={}
    for k,v in items:
        need(isinstance(k,Node) and k.level==level-1 and 0<=v<9,'address/digit')
        if v==default:d.pop(k,None)
        else:d[k]=v
    if level<=2:
        need(default==0,'canonical small default')
    else:need(capped_sites(level-1,2*len(d)+1)>2*len(d),'unique majority baseline')
    return Node(level,default,tuple(sorted(d.items(),key=lambda kv:repr(kv[0]))))
def demand(n,key,clock):
    need(key.level==n.level-1,'typed demand')
    for k,v in n.overrides:
        clock[0]+=1
        if key==k:return v
    return n.default
@dataclass(frozen=True)
class Program:
    level:int; default:int; writes:tuple
    def compile(self):return make(self.level,self.default,self.writes)
    def receipt(self):
        n=self.compile()
        # Store original ordered writes independently from semantic key.
        return n,self.writes,(len(self.writes),len(n.overrides))

def tower():
    l1=[make(1,0,[(UNIT,i)]) for i in range(9)]
    keys=[make(2,0,zip(l1,[(i+j)%9 for j in range(9)])) for i in range(9)]
    for i,k in enumerate(keys):
        for j,a in enumerate(l1):need(demand(k,a,[0])==(i+j)%9,'level2 exact')
    a,history,cost=Program(3,2,((keys[0],7),(keys[1],0),(keys[0],8))).receipt()
    need(cost==(3,2) and history[0][1]==7,'retained overwritten history')
    need(a==make(3,2,[(keys[1],0),(keys[0],8)]),'canonical last write')
    clock=[0];need([demand(a,k,clock) for k in keys]==[8,0]+[2]*7,'level3 sparse zero/default')
    b=make(4,4,[(a,0)]);c=make(5,1,[(b,8)])
    need(demand(c,b,clock)==8 and demand(b,a,clock)==0,'deep demand')
    need(capped_sites(2,10**9)==387420489 and capped_sites(3,100)==100,'capped cardinality')
    print('H12 level5 demand, 81 level2 checks, lookup comparisons',clock[0],'no dense tower',flush=True)

def strip(w,n,labels,vertical,horizontal,left=None,right=None):
    need(w>0 and n>0 and labels>1,'strip dimensions')
    need(vertical.shape==(n,w-1) and horizontal.shape==(n-1,w),'edge shapes')
    need(np.issubdtype(vertical.dtype,np.signedinteger) and np.issubdtype(horizontal.dtype,np.signedinteger),'integer weights')
    bound=sum(abs(int(x)) for x in vertical.flat)+sum(abs(int(x)) for x in horizontal.flat)
    need(4*bound+1<2**63,'checked integer bound')
    bad=-2*bound-1
    states=np.array(list(product(range(labels),repeat=w)),dtype=np.int64); m=len(states)
    for b in (left,right):
        if b is not None:need(len(b)==w and all(0<=x<labels for x in b),'boundary labels')
    vscore=lambda row:((states[:,1:]!=states[:,:-1])*vertical[row]).sum(axis=1)
    val=vscore(0); pred=[]
    if left is not None:val=np.where(np.all(states==left,axis=1),val,bad)
    for j in range(1,n):
        edge=((states[:,None,:]!=states[None,:,:])*horizontal[j-1]).sum(axis=2)
        z=val[:,None]+edge; ix=z.argmax(axis=0); val=z[ix,np.arange(m)]+vscore(j);pred.append(ix)
    if right is not None:val=np.where(np.all(states==right,axis=1),val,bad)
    k=int(val.argmax());best=int(val[k]);ids=[k]
    for ix in reversed(pred):k=int(ix[k]);ids.append(k)
    return best,states[ids[::-1]],(n-1)*m*m

def score(a,v,h):return int(((a[:,1:]!=a[:,:-1])*v).sum()+((a[1:]!=a[:-1])*h).sum())
def reduction():
    v=np.array([[2,-1],[0,2],[-2,1]]);h=np.array([[1,-2,2],[0,1,-1]])
    for l in (2,3):
        best,a,cost=strip(3,3,l,v,h)
        brute=max(score(np.array(x).reshape(3,3),v,h) for x in product(range(l),repeat=9))
        need(best==brute==score(a,v,h),'full witness')
        for left,right in product(product(range(l),repeat=3),repeat=2):
            best,a,_=strip(3,3,l,v,h,left,right)
            ref=max(score(np.array([left,m,right]),v,h) for m in product(range(l),repeat=3))
            need(best==ref==score(a,v,h),'conditioned interface witness')
        print('H15 labels',l,'boundary tables',l**6,'dense brute',l**9,'DP candidates',cost,flush=True)
    n=128; v=np.arange(n*2).reshape(n,2)%5-2;h=np.arange((n-1)*3).reshape(n-1,3)%5-2
    best,a,cost=strip(3,n,3,v,h);need(best==score(a,v,h),'large witness')
    print('H15 width3 length128 candidates',cost,'witness',best,flush=True)

if __name__=='__main__':
    fields();renderer();tower();reduction()
