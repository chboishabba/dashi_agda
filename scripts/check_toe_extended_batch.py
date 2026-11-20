"""Paired Q(zeta3)[i] scalar lift using the existing cubic batch executor."""
import numpy as np
from toe_cyclotomic_hom_batch import apply_batch
from toe_cyclotomic_operator import compile_shape,points
import check_toe_atlas_mirror as M

def act(state, name, adj=False, wrong=False):
    phase,v,den=state
    target=3-phase if name=='s' else phase
    source=target if adj else phase
    out,d=apply_batch(records[name,source],v,adjoint=adj)
    if name=='r':
        a,b=np.split(out,2,axis=2)
        sign=(1 if phase==1 or wrong else -1)*(-1 if adj else 1)
        out=np.concatenate((-sign*b,sign*a),axis=2)
    return target,out,den*d

def same(a,b):
    return a[0]==b[0] and np.array_equal(a[1]*b[2],b[1]*a[2])

A=M.inv(M.Pa)@M.r@M.Pa%3; B=M.inv(M.Pa)@M.m@M.Pa%3
records={(name,s):dict(compile_shape(G,lam,s),scalar=g) for s in (1,2) for name,G,lam,g in [('r',A,1,[1,0,27]),('s',B,2,[1,0,1])]}
X=points(6); parity=(-X%3)@3**np.arange(5,-1,-1)
v=np.random.default_rng(41).integers(-2,3,(2,729,180)).astype(object)
for s in (1,2):
    x=(s,v,1); r=act(x,'r'); r2=act(r,'r'); r3=act(r2,'r')
    assert same(r2,(s,-v[:,parity],1))
    assert same(act(r3,'r'),x)
    assert same(act(r,'r',adj=True),x)
    assert same(act(act(x,'s'),'s'),x)
    assert same(act(act(act(x,'s'),'r'),'s'),r3)
    assert not same(act(act(act(x,'s'),'r',wrong=True),'s'),act(x,'r',adj=True,wrong=True))
    print('PASS phase',s,'65610 extended coordinates; negative parity, D4, adjoint, wrong-gauge rejection',flush=True)
