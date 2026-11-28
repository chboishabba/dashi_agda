"""Compiled evaluator for the exact BN interval expression graph.
No fastmath, no rounding-mode changes. Each elementary operation is enclosed
with nextafter as in the reference interval evaluator; zero/one identities exact.
"""
from fractions import Fraction as Q
from math import factorial
import numpy as np
import numba as nb
import check_hopf369_p0bn as bn
from check_hopf369_p0bn_radial import bounds
OldI=bn.I; J=bn.J

class Graph:
    def __init__(self):self.nodes=[];self.cache={};self.constants={};self.inputs=[]
    def node(self,op,a,b=0,lo=0.,hi=0.):
        key=(op,a,b,lo,hi)
        if key not in self.cache:
            self.cache[key]=len(self.nodes);self.nodes.append(key)
        return self.cache[key]
    def const(self,a,b=None):
        a=float(a);b=a if b is None else float(b);n=self.node(0,0,0,a,b);self.constants[n]=(a,b);return n
    def input(self):
        n=self.node(1,len(self.inputs));self.inputs.append(n);return GI.fromid(n)
    def compute(self,op,a,b=0):
        ca=self.constants.get(a);cb=self.constants.get(b)
        if op==2:
            if ca==(0.,0.):return b
            if cb==(0.,0.):return a
        if op==3:
            if ca==(0.,0.) or cb==(0.,0.):return self.const(0)
            if ca==(1.,1.):return b
            if cb==(1.,1.):return a
        if ca is not None and (op not in (2,3) or cb is not None):
            l,h=ca; down=lambda x:np.nextafter(x,-np.inf);up=lambda x:np.nextafter(x,np.inf)
            if op==2:return self.const(down(l+cb[0]),up(h+cb[1]))
            if op==3:
                p=[l*cb[0],l*cb[1],h*cb[0],h*cb[1]];return self.const(down(min(p)),up(max(p)))
            if op==4:return self.const(-h,-l)
            if op==5:
                assert not l<=0<=h;return self.const(down(1/h),up(1/l))
            if op==6:return self.const(0 if l<=0<=h else max(0,down(min(l*l,h*h))),up(max(l*l,h*h)))
            if op==7:
                assert l>0;return self.const(down(np.sqrt(l)),up(np.sqrt(h)))
        if op in (2,3) and b<a:a,b=b,a
        return self.node(op,a,b)
    def compile(self,last):
        used=set();stack=[last]
        while stack:
            k=stack.pop()
            if k in used:continue
            used.add(k);op,a,b,*_=self.nodes[k]
            if op>=2:stack.append(a)
            if op in (2,3):stack.append(b)
        ids=sorted(used);remap={k:i for i,k in enumerate(ids)}
        ops=[];args=[];const=[]
        for k in ids:
            op,a,b,lo,hi=self.nodes[k];ops.append(op);args.append((remap[a] if op>=2 else a,remap[b] if op in (2,3) else 0));const.append((lo,hi))
        return np.array(ops,np.int8),np.array(args,np.int32),np.array(const),remap[last]
G=None
class GI:
    def __init__(self,a,b=None):self.id=G.const(a,b)
    @staticmethod
    def fromid(n):x=GI.__new__(GI);x.id=n;return x
    @staticmethod
    def of(x):
        if isinstance(x,GI):return x
        if isinstance(x,Q):
            v=float(x);return GI(np.nextafter(v,-np.inf),np.nextafter(v,np.inf))
        if isinstance(x,OldI):return GI(x.a,x.b)
        return GI(x)
    def __add__(self,x):
        if isinstance(x,J):return NotImplemented
        return GI.fromid(G.compute(2,self.id,GI.of(x).id))
    __radd__=__add__
    def __neg__(self):return GI.fromid(G.compute(4,self.id))
    def __sub__(self,x):return self+-x if isinstance(x,(GI,J)) else self+-GI.of(x)
    def __rsub__(self,x):return -self+x
    def __mul__(self,x):
        if isinstance(x,J):return NotImplemented
        return GI.fromid(G.compute(3,self.id,GI.of(x).id))
    __rmul__=__mul__
    def inv(self):return GI.fromid(G.compute(5,self.id))
    def __truediv__(self,x):return self*GI.of(x).inv()
    def __rtruediv__(self,x):return self.inv()*x
    def sqrt(self):return GI.fromid(G.compute(7,self.id))
    def __pow__(self,n):
        if n<0:return self.inv()**(-n)
        if n==0:return GI(1)
        if n==1:return self
        if n%2==0:return GI.fromid(G.compute(6,self.id))**(n//2)
        return self*self**(n-1)

def graph_hyper(y):
    # Input y-L/2 is always in [-1,1] by construction of the sweep.
    q=y.get(bn.zero);ch=sum((q**(2*k)/factorial(2*k) for k in range(10)),GI(0))+GI(-1,1)*GI.of(Q(2,factorial(20)))
    sh=sum((q**(2*k+1)/factorial(2*k+1) for k in range(9)),GI(0))+GI(-1,1)*GI.of(Q(2,factorial(19)))
    return J({(0,0,0,k):(ch if k%2==0 else sh)/factorial(k) for k in range(y.k+1)},y.k)

def build(data,shift):
    global G;G=Graph();old={k:getattr(bn,k) for k in ('I','h','j','L','eps','sinhcosh')}
    try:
        bn.I=GI
        for k in ('h','j','L','eps'):setattr(bn,k,GI(old[k].a,old[k].b))
        bn.sinhcosh=graph_hyper
        r=G.input();y=G.input();co=G.input();si=G.input();keys=[]
        def get(e,i,a):
            key=str((e,i,a));v=data[key]
            if np.all(v==0):return GI(0)
            keys.append(key);return G.input()
        a=[J({a:co*get(0,i,a)+si*get(1,i,a) for a in bn.idx[3] if a[3]==0},3) for i in range(3)]
        out=bn.quotient([r,GI(0),y],GI.of(shift),source_jets=a)
        args=G.compile(out.id);print('graph nodes',len(args[0]),'inputs',len(G.inputs),flush=True);return args,keys
    finally:
        for k,v in old.items():setattr(bn,k,v)

@nb.njit(parallel=True,fastmath=False,cache=True)
def eval_graph(ops,args,const,last,inputs):
    out=np.empty((len(inputs),2))
    for k in nb.prange(len(inputs)):
        l=np.empty(len(ops));h=np.empty(len(ops));valid=True
        for j in range(len(ops)):
            op=ops[j];a,b=args[j]
            if op==0:l[j]=const[j,0];h[j]=const[j,1]
            elif op==1:l[j]=inputs[k,a,0];h[j]=inputs[k,a,1]
            elif op==2:l[j]=np.nextafter(l[a]+l[b],-np.inf);h[j]=np.nextafter(h[a]+h[b],np.inf)
            elif op==3:
                p=l[a]*l[b];q=l[a]*h[b];r=h[a]*l[b];s=h[a]*h[b];l[j]=np.nextafter(min(p,q,r,s),-np.inf);h[j]=np.nextafter(max(p,q,r,s),np.inf)
            elif op==4:l[j]=-h[a];h[j]=-l[a]
            elif op==5:
                if l[a]<=0<=h[a]:valid=False;break
                l[j]=np.nextafter(1/h[a],-np.inf);h[j]=np.nextafter(1/l[a],np.inf)
            elif op==6:
                p=l[a]*l[a];q=h[a]*h[a];l[j]=0. if l[a]<=0<=h[a] else max(0.,np.nextafter(min(p,q),-np.inf));h[j]=np.nextafter(max(p,q),np.inf)
            elif op==7:
                if l[a]<=0:valid=False;break
                l[j]=np.nextafter(np.sqrt(l[a]),-np.inf);h[j]=np.nextafter(np.sqrt(h[a]),np.inf)
            if not np.isfinite(l[j]) or not np.isfinite(h[j]):valid=False;break
        if valid:out[k,0]=l[last];out[k,1]=h[last]
        else:out[k,0]=-np.inf;out[k,1]=np.inf
    return out

def cover(depth,shift,data,boxes=None,graph=None,keys=None):
    n=2**depth
    if graph is None:graph,keys=build(data,shift)
    if boxes is None:boxes=np.indices((n,n,n),dtype=np.int32).reshape(3,-1).T
    ri,ai,yi=boxes.T;ang=OldI(ai/n,(ai+1)/n);lo=OldI(ai/n);hi=OldI((ai+1)/n)
    co=OldI(((1-hi**2)/(1+hi**2)).a,((1-lo**2)/(1+lo**2)).b)
    si=OldI((2*lo/(1+lo**2)).a,(2*hi/(1+hi**2)).b)
    ins=np.stack([np.stack([ri/n,(ri+1)/n],axis=1),np.stack([yi/n,(yi+1)/n],axis=1),np.stack([co.a,co.b],axis=1),np.stack([si.a,si.b],axis=1)]+[data[k][ri] for k in keys],axis=1)
    vals=eval_graph(*graph,ins);m=-vals[:,1] if shift>0 else vals[:,0];good=m>0;print('compiled sweep',depth,shift,'pass',int(good.sum()),'remaining',int((~good).sum()),'min paid margin',float(np.min(m[good])) if np.any(good) else None,'range',vals[:,0].min(),vals[:,1].max(),flush=True)
    return boxes[~good],vals,graph,keys

if __name__=='__main__':
    import sys,time
    depth=int(sys.argv[1]) if len(sys.argv)>1 else 5;start=time.monotonic();data=bounds(depth)
    nb.set_num_threads(min(4,nb.get_num_threads()))
    for shift,margin in [(Q(-2,25),Q(43724,100000)),(Q(2,25),Q(44424,100000))]:
        rem,vals,_,_=cover(depth,shift,data);assert not len(rem)
        m=np.min(vals[:,0]) if shift<0 else -np.max(vals[:,1]);assert Q(float(m))>margin
    print('PASS full-domain ordered barriers; elapsed seconds',time.monotonic()-start,flush=True)
