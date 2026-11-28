#!/usr/bin/env python3
"""Source compression trace fibre and repeated compatible strip elimination."""
from itertools import product
import numpy as np
import sympy as s
from check_h08_h11_h12_h15 import Field, need, strip, score

def trace_fibres():
    h=Field((2,2,0)); hs=list(product(range(3),repeat=3)); counts=[]
    for f,g in ((Field((2,0,0,0,1,0,0,0,0)),None),(Field((1,0,0,0,1,1)),(0,1,0,1,1,0))):
        if g is None:g=f.primitive()
        orbit=f.orbit(g); logs={a:i for i,a in enumerate(orbit)}; m=f.size-1
        r=f.cubic_root(orbit); sub={a:f.embed(a,r) for a in hs}; subinv={v:k for k,v in sub.items()}
        def trace(a):
            if a==f.zero:return f.zero
            z=f.zero
            for j in range(f.n//3):z=f.add(z,orbit[(logs[a]*27**j)%m])
            return z
        theta=next(a for a in orbit if trace(a)==f.one)
        step=orbit[m//26]; step_code=subinv[step]
        def minus(a):return tuple(-v%3 for v in a)
        def encode(a):
            t=trace(a); k=f.add(a,minus(f.mul(theta,t)))
            return subinv[t],k
        def decode(t,k):return f.add(f.mul(theta,sub[t]),k)
        kernel=set(); bad=0
        for a in [f.zero]+orbit:
            t,k=encode(a);kernel.add(k)
            need(trace(k)==f.zero and decode(t,k)==a,'trace split BIDI')
            tt,kk=encode(f.mul(step,a))
            need(tt==h.mul(step_code,t) and kk==f.mul(step,k),'subfield action equivariance')
            if trace(a)==f.zero and trace(f.mul(g,a))!=f.zero:bad+=1
        need(len(kernel)==3**(f.n-3) and bad>0,'kernel and full multiplier negative control')
        if f.n==9:need(all(trace(a)==f.zero for a in sub.values()),'degree3 subfield trace vanishes')
        else:
            T=s.Matrix([[-1,-1,0,1,1,-1],[0,0,0,1,1,-1],[-1,1,0,0,0,0],[1,-1,0,-1,-1,-1],[0,0,1,1,1,-1],[0,0,1,-1,1,1]])
            Q=s.Matrix([[1,1,0,1,0,0],[0,-1,0,1,-1,-1],[0,0,1,1,0,1],[0,1,1,-1,0,-1],[0,-1,-1,0,-1,-1],[0,-1,-1,-1,-1,-1]])
            A=np.array(Q,dtype=np.int64); R=np.array((T**28).applyfunc(lambda a:int(a)%3),dtype=np.int64)
            for x in product(range(3),repeat=6):
                y=tuple(A@np.array(x)%3); z=tuple(A@(R@np.array(x)%3)%3)
                need(z==f.mul(step,y),'literal source T^28 intertwiner')
        counts.append((f.n,f.size,len(kernel),theta,bad))
    print('trace split degree,states,kernel,section,full-step failures',counts,flush=True)

class Segment:
    def __init__(self, table, left=None, right=None, arg=None):
        self.table=table;self.left=left;self.right=right;self.arg=arg
    def join(self,other):
        z=self.table[:,:,None]+other.table[None,:,:]
        arg=z.argmax(axis=1); m=len(arg)
        return Segment(z[np.arange(m)[:,None],arg,np.arange(m)[None,:]],self,other,arg)
    def reopen(self,a,b):
        if self.arg is None:return [a,b]
        k=int(self.arg[a,b]);return self.left.reopen(a,k)[:-1]+self.right.reopen(k,b)

def batch(w,n,l,v,h):
    need(n>=2 and w>=1,'strip batch dimensions')
    need(v.shape==(n,w-1) and h.shape==(n-1,w),'edge shapes')
    need(np.issubdtype(v.dtype,np.signedinteger) and np.issubdtype(h.dtype,np.signedinteger),'integer weights')
    need(sum(abs(int(x)) for x in v.flat)+sum(abs(int(x)) for x in h.flat)<2**62,'checked score bound')
    states=np.array(list(product(range(l),repeat=w)),dtype=np.int64);m=len(states)
    vs=((states[None,:,1:]!=states[None,:,:-1])*v[:,None,:]).sum(axis=2)
    leaves=[Segment(((states[:,None,:]!=states[None,:,:])*h[j]).sum(axis=2)+vs[j+1][None,:]) for j in range(n-1)]
    rounds=[len(leaves)];work=0
    while len(leaves)>1:
        work+=(len(leaves)//2)*m**3
        leaves=[leaves[i].join(leaves[i+1]) if i+1<len(leaves) else leaves[i] for i in range(0,len(leaves),2)]
        rounds.append(len(leaves))
    root=leaves[0];return root,root.table+vs[0][:,None],states,rounds,work

def reduction():
    v=np.array([[2,-1],[0,2],[-2,1]]);h=np.array([[1,-2,2],[0,1,-1]])
    count=0
    for l in (2,3):
        root,t,states,rounds,work=batch(3,3,l,v,h)
        for a,b in product(range(len(states)),repeat=2):
            witness=states[root.reopen(a,b)];ref,_,_=strip(3,3,l,v,h,states[a],states[b])
            need(score(witness,v,h)==t[a,b]==ref,'full conditional batch witness');count+=1
    n=128;v=np.arange(n*2).reshape(n,2)%5-2;h=np.arange((n-1)*3).reshape(n-1,3)%5-2
    root,t,states,rounds,work=batch(3,n,3,v,h);a,b=np.unravel_index(t.argmax(),t.shape)
    witness=states[root.reopen(a,b)];ref,_,_=strip(3,n,3,v,h)
    need(score(witness,v,h)==t[a,b]==ref,'balanced full witness')
    print('H15 balanced',count,'conditioned tables; rounds',rounds,'candidates',work,'score',ref,flush=True)

if __name__=='__main__':trace_fibres();reduction()
