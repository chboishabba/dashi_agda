#!/usr/bin/env python3
"""Retained Coxeter defect histories; not a Monster representation."""
from pathlib import Path
from runpy import run_path
from itertools import product, permutations
from functools import lru_cache
from dataclasses import dataclass, replace
import numpy as np
import sympy as S
src=run_path(str(Path(__file__).with_name('check_y443_incidence_coxeter_20261125.py')))
require=src['require']; R=src['R']; Q=src['Q']; image=src['image']; word=src['word']
J=S.eye(12); spider=tuple(src['spider'])*10; central=tuple(src['central'])*9
H=word(spider,Q); C=word(central,Q); U=H-J; V=C-J
require([U.rank(),(U**2).rank(),(U**3).rank()]==[2,1,0],'spider filtration')
Ep=(J+C)/2; Em=(J-C)/2
require(Ep**2==Ep and Em**2==Em and Ep*Em==S.zeros(12) and Ep+Em==J,'signed split')
require((Ep.rank(),Em.rank())==(5,7),'signed dimensions')
for n in range(-12,13):
    require(H**n==J+n*U+(n*(n-1)//2)*U**2,'signed winding')
def closure(seed):
    W=S.Matrix.hstack(*seed.columnspace()); ranks=[W.cols]
    while True:
        T=S.Matrix.hstack(*S.Matrix.hstack(W,*[q*W for q in Q]).columnspace())
        if T.cols==W.cols: return ranks
        W=T; ranks.append(W.cols)
rs=closure(U); rc=closure(V)
require(rs[-1]==rc[-1]==12,'invariant closure')
# Exact bounded int64 rank-one updates: check overflow bound before each update.
Id=np.eye(26,dtype=np.int64); actors=[np.array(a.tolist(),dtype=np.int64) for a in R]
loops=[(),spider,central,spider+central,central+spider,spider+spider[::-1],central+central]
def frame(b,k):
    return np.argsort([13*((t//13)^b)+(((-1)**b*(t%13)+k)%13) for t in range(26)])
def chart(a,p): return a[np.ix_(p,p)]
def pack(a): return a.tobytes()
def unpack(a): return np.frombuffer(a,dtype=np.int64).reshape(26,26)
@lru_cache(None)
def evaluate(w,b,k):
    ar=[chart(a,frame(b,k)) for a in actors]; m=Id.copy(); d=np.zeros_like(Id); hist=[]
    for i in w:
        a=ar[i]; e=a-Id; j=next(j for j in range(26) if any(e[j,:])); bound=max(int(np.abs(m).max()),int(np.abs(d).max())); eb=int(np.abs(e).max()); require(bound+eb+bound*eb<2**62,'integer update bound'); m=m+np.outer(m[:,j],e[j,:]); d=d+e+np.outer(d[:,j],e[j,:]); hist.append(pack(d))
    require(np.array_equal(m,Id+d),'independent word and defect')
    return pack(m),pack(d),tuple(hist)
T=frame(0,1)
@lru_cache(None)
def shift(a):return pack(chart(unpack(a),T))
@dataclass(frozen=True)
class State:
    w:tuple; b:int; k:int; probe:tuple; meta:tuple
    operator:object=None; residual:object=None

def x(q):return replace(q,operator=evaluate(q.w,q.b,q.k)[0])
def y(q):
    _,d,h=evaluate(q.w,q.b,q.k); return replace(q,residual=(d,h,tuple(unpack(d)@q.probe)))
def z(q):
    a=None if q.operator is None else shift(q.operator)
    d=None if q.residual is None else (shift(q.residual[0]),tuple(shift(m) for m in q.residual[1]),tuple(q.residual[2][i] for i in T))
    return replace(q,k=(q.k+1)%13,probe=tuple(q.probe[i] for i in T),operator=a,residual=d)
def path(q,order):
    for c in order:q={'x':x,'y':y,'z':z}[c](q)
    return q
faces=ends=0
for b,k in product(range(2),range(13)):
    for w in loops:
        for sign in (-1,0,1):
            q=State(w,b,k,tuple(sign*Id[:,image[0]][frame(b,k)]),('history',17,3,2,1))
            for a,c,d in (('x','y','z'),('x','z','y'),('y','z','x')):
                for pre in ('',d):
                    require(path(q,pre+a+c)==path(q,pre+c+a),'six faces'); faces+=1
            target=path(q,'xyz')
            for o in permutations('xyz'):
                require(path(q,o)==target,'six endpoints'); ends+=1
            require(target.operator==pack(Id+unpack(target.residual[0])) and target.w==w and target.meta==q.meta,'recover history')
require(evaluate(loops[0],0,0)[0]==evaluate(loops[5],0,0)[0]==evaluate(loops[6],0,0)[0]==pack(Id),'return collision')
F=unpack(evaluate(spider,0,0)[0]); G=unpack(evaluate(central,0,0)[0]); D=F-Id; E=G-Id
require(26*max(int(np.abs(F).max()),int(np.abs(G).max()),int(np.abs(D).max()),int(np.abs(E).max()))**2+2**20<2**62,'product bound')
require(np.array_equal(F@G-Id,D+E+D@E) and not np.array_equal(F@G,G@F),'ordered product law')
require(np.array_equal(D@np.zeros(26,dtype=np.int64),E@np.zeros(26,dtype=np.int64)),'zero probe collision')
print('PASS spider closure',rs,'central closure',rc,'central signs 5/7; signed winding -12..12')
print('PASS',faces,'six-face comparisons;',ends,'endpoint paths; zero and signed probes; ordered defects')
