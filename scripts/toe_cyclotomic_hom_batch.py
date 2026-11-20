"""Cached C3 butterfly action on H tensor multiplicity, not actual Monster recognition."""
import json
from functools import lru_cache
import numpy as np
from toe_cyclotomic_butterfly import plan, butterfly, root
from toe_cyclotomic_operator import load

@lru_cache(maxsize=16)
def cached(payload):
    R=load(payload)
    blocks=tuple(tuple(tuple(int(i) for i in a) for a in block) for block in plan(R))
    N=3**len(R['origin'])
    for axis in (0,1):
        if sorted(i for block in blocks for i in block[axis])!=list(range(N)):
            raise ValueError('not a partition')
    return blocks

def apply_batch(R,vector,adjoint=False):
    payload=json.dumps(R,sort_keys=True,separators=(',',':'))
    R=load(payload); N=3**len(R['origin']); r=R['rank']; g,h,d=R['scalar']
    v=np.asarray(vector,dtype=object)
    if v.ndim!=3 or v.shape[:2]!=(2,N) or any(type(x)!=int for x in v.flat):
        raise ValueError('integer pair vector with multiplicity axis required')
    out=np.zeros_like(v)
    for xi,yi,pre,post,freq in cached(payload):
        if not adjoint:
            z=butterfly([root(tuple(v[:,j]),k) for j,k in zip(xi,pre)],r)
            for y,k,f in zip(yi,post,freq):
                a,b=root(z[f],k); out[:,y]=[a*g-b*h,a*h+b*g-b*h]
        else:
            z=[None]*len(freq)
            for y,k,f in zip(yi,post,freq):
                a,b=root(tuple(v[:,y]),-k)
                z[f]=(a-b,-b)
            z=butterfly(z,r)
            for x,k,(a,b) in zip(xi,pre,z):
                a,b=root((a-b,-b),-k); gg,hh=g-h,-h
                out[:,x]=[a*gg-b*hh,a*hh+b*gg-b*hh]
    return out,d
