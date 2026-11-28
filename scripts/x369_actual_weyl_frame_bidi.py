"""Matrix-free exact Weyl-frame BIDI for actual right MMV modules over F7.

Reuse actual mmgroup group words, not a synthetic representation. The
joint weight-zero projection and rank proof apply to the same group action.
Rank is computed over F7, never floating point. Both prime-local frames
have an explicit inverse on every admitted vector. Source completeness
uses independent source eigenspace dimension and actual Weyl relations.
"""
from dataclasses import dataclass
from itertools import product
from time import monotonic
import hashlib
import numpy as np


def require(ok,msg):
    if not ok:raise ValueError(msg)


def coords(v):
    a=np.asarray(v['E'],dtype=np.int16).reshape(-1)%7
    require(len(a)==196884,'actual weight-two source dimension')
    return a


def source_sha(v):
    return hashlib.sha256(coords(v).astype(np.uint8).tobytes()).hexdigest()


class RowBasis:
    def __init__(self):
        self.rows=[];self.pivots=[]

    def add(self,arr):
        a=np.asarray(arr,dtype=np.int16).copy()%7
        for k,row in zip(self.pivots,self.rows):
            if a[k]:a=(a-int(a[k])*row)%7
        nz=np.flatnonzero(a)
        if not len(nz):return False
        k=int(nz[0]);a=(a*pow(int(a[k]),-1,7))%7
        self.pivots.append(k);self.rows.append(a)
        return True


def inverse7(matrix):
    a=np.asarray(matrix,dtype=np.int64).copy()%7
    n=len(a)
    require(a.shape==(n,n),'square pivot matrix')
    a=np.concatenate((a,np.eye(n,dtype=np.int64)),axis=1)
    for j in range(n):
        k=next((i for i in range(j,n) if a[i,j]),None)
        require(k is not None,'singular seed pivot matrix')
        a[[j,k]]=a[[k,j]]
        a[j]=(a[j]*pow(int(a[j,j]),-1,7))%7
        for i in range(n):
            if i!=j:a[i]=(a[i]-a[i,j]*a[j])%7
    return a[:,n:]


@dataclass
class WeylFrame:
    prime: int
    zeta: int
    center: object
    A: tuple
    B: tuple
    seeds: list
    labels: list
    rank: RowBasis

    def __post_init__(self):
        require(self.prime in (2,3) and pow(self.zeta,self.prime,7)==1 and
                self.zeta!=1 and len(self.A)==len(self.B),'Weyl frame scope')

    def project(self,v,weight=None):
        p=self.prime
        if weight is None:weight=(0,)*len(self.B)
        require(len(weight)==len(self.B) and all(0<=t<p for t in weight),'weight')
        def eig(w,g,k):
            # P_k = p^-1 sum zeta^(-kt) g^t, right module.
            out=w;v=w
            for t in range(1,p):
                v=v*g;out=out+pow(self.zeta,(-k*t)%p,7)*v
            return pow(p,-1,7)*out
        w=eig(v,self.center,1)
        for b,k in zip(self.B,weight):w=eig(w,b,k)
        return w

    def admit(self,v,label):
        w=self.project(v)
        if w==0*w:return False
        require(w*self.center==self.zeta*w and all(w*b==w for b in self.B),
                'source joint projector failed')
        if not self.rank.add(coords(w)):return False
        self.seeds.append(w);self.labels.append(list(label))
        return True

    def translate(self,v,u):
        require(len(u)==len(self.A) and all(type(t) is int and 0<=t<self.prime for t in u),'weight index')
        # B_i A_i = z A_i B_i in the ternary source; binary sign
        # is symmetric. Right-module A^-u yields eigenphase zeta^u.
        for a,t in zip(self.A,u):
            if t:v=v*(a**(-t))
        return v

    def untranslate(self,v,u):
        return self.translate(v,tuple((-t)%self.prime for t in u))

    def column(self,u,j):
        require(type(j) is int and 0<=j<len(self.seeds),'multiplicity index')
        return self.translate(self.seeds[j],u)

    def pivot_inverse(self):
        return inverse7(np.stack([coords(v)[self.rank.pivots] for v in self.seeds],axis=1))

    def zero_coordinates(self,v,inv=None):
        if inv is None:inv=self.pivot_inverse()
        c=(inv@coords(v)[self.rank.pivots])%7
        w=0*v
        for a,s in zip(c,self.seeds):
            if a:w=w+int(a)*s
        require(w==v,'weight-zero vector outside declared seed span')
        return tuple(map(int,c))

    def read_weight(self,v,u,inv=None):
        require(v*self.center==self.zeta*v,'not selected central phase')
        # Pull back only this character sector, not a dense 98304-square matrix.
        return self.zero_coordinates(self.untranslate(self.project(v,u),u),inv)

    def reopen(self,coefficients):
        require(bool(self.seeds),'empty seed basis')
        w=0*self.seeds[0]
        for u,c in coefficients.items():
            require(len(c)==len(self.seeds) and all(type(x) is int and 0<=x<7 for x in c),'field coordinates')
            s=0*self.seeds[0]
            for a,v in zip(c,self.seeds):
                if a:s=s+a*v
            w=w+self.translate(s,u)
        return w

    def split(self,v,*,weights=None):
        # Full inverse is finite but costly: caller may request individual
        # weight sectors. Never call a partial split a whole-vector inverse.
        inv=self.pivot_inverse()
        full=weights is None
        if full:weights=product(range(self.prime),repeat=len(self.A))
        out={}
        for u in weights:
            u=tuple(u);c=self.read_weight(v,u,inv)
            if any(c):out[u]=c
        if full:require(self.reopen(out)==v,'full source Weyl inverse')
        return out

    def verify_seed(self,j,deadline):
        s=self.seeds[j];n=len(self.A);p=self.prime;checks=0
        require(s*self.center==self.zeta*s and all(s*b==s for b in self.B),'seed eigenspace')
        for i in range(n):
            if monotonic()>=deadline:return checks,False
            u=tuple(int(i==k) for k in range(n));v=self.column(u,j)
            require(self.untranslate(v,u)==s,'translation inverse')
            require(v*self.center==self.zeta*v,'translation central phase')
            for k,b in enumerate(self.B):
                require(v*b==(self.zeta if i==k else 1)*v,'actual Weyl weight')
                checks+=1
        return checks,True

    def check_bidi(self):
        n=len(self.A);inv=self.pivot_inverse()
        zero=(0,)*n;u=(1,)+(0,)*(n-1)
        c0=tuple((j+1)%7 for j in range(len(self.seeds)))
        c1=tuple((2*j+1)%7 for j in range(len(self.seeds)))
        v=self.reopen({zero:c0,u:c1})
        require(self.read_weight(v,zero,inv)==c0 and self.read_weight(v,u,inv)==c1,
                'actual mixed weight BIDI')
        require(self.reopen({zero:self.read_weight(v,zero,inv),u:self.read_weight(v,u,inv)})==v,
                'actual two-weight inverse')
        return True
