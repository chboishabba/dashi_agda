"""Source-first compiler and independent serialized streaming execution regression."""
import json
import numpy as np
from toe_cyclotomic_operator import compile_shape,load,apply,points,columns
import check_toe_atlas_mirror as M
X=points(6); N=len(X); e=np.zeros((2,N),dtype=object);e[0,0]=1
A=M.inv(M.Pa)@M.P%3; Ra=M.inv(M.Pa)@M.r@M.Pa%3; Ma=M.inv(M.Pa)@M.m@M.Pa%3
R=M.inv(M.P)@M.r@M.P%3; S=M.inv(M.P)@M.m@M.P%3

def rec(A,lam,s,g):
    return load(json.dumps(dict(compile_shape(A,lam,s),scalar=list(g))))
def gauge(A,lam,s,vec,den):
    shape=compile_shape(A,lam,s); idx=int(np.array(shape['origin'])@3**np.arange(5,-1,-1)); return tuple(int(x) for x in vec[:,idx])+(den,)
k=rec(A,1,1,(-1,-2,27)); km=rec(A,1,2,(1,2,27))
f=rec(Ra,1,1,(1,0,27)); mirror=rec(Ma,2,1,(1,0,1))
v,d=apply(k,e); v2,d2=apply(f,v); vr,d3=apply(k,v2,adjoint=True)
rr=rec(R,1,1,gauge(R,1,1,vr,d*d2*d3))
vs,d4=apply(km,v,adjoint=True); ss=rec(S,2,1,gauge(S,2,1,vs,d*d4))
# Independent dense oracle imported only after source compilation.
import check_toe_atlas_composed as D
cases=[(mirror,D.identity,1,Ma,2),(ss,D.S,D.sd,S,2),(k,D.entrymul(D.k,(-1,-2)),27,A,1),(rr,D.R,D.rd,R,1)]
rng=np.random.default_rng(123); count=0
for record,H,den,G,lam in cases:
    for s in (1,2):
        g,h,d=record['scalar']; recs=record if s==1 else rec(G,lam,2,(g-h,-h,d)); oracle=H if s==1 else D.conj(H)
        for j,y,pair in columns(recs):
            assert np.count_nonzero((oracle[0][:,j]!=0)|(oracle[1][:,j]!=0))==len(y)
            assert len(set(y))==len(y)
            for i in (0,1): assert np.array_equal(pair[i]*den,oracle[i][y,j].astype(object)*recs['scalar'][2])
            count+=N
        v=rng.integers(-2,3,size=(2,N)).astype(object); out,d=apply(recs,v); want=D.mul(oracle,(v[0][:,None],v[1][:,None])); assert all(np.array_equal(out[i]*den,want[i][:,0]*d) for i in (0,1))
        out,d=apply(recs,v,adjoint=True); want=D.mul(D.adj(oracle),(v[0][:,None],v[1][:,None])); assert all(np.array_equal(out[i]*den,want[i][:,0]*d) for i in (0,1))
    print('PASS rank',record['rank'],'both phases, dense oracle, streaming forward and adjoint',flush=True)
print('PASS',count,'coefficient positions')
