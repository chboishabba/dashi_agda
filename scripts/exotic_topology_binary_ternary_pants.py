#!/usr/bin/env python3
"""Exact finite Cantor-prefix codec / pants-frontier cross-pollination.

Three-symbol code: 3->0, 6->10, 9->11. Finite prefix-code
antichains at every depth are checked; Kraft dyadic masses sum to 1.
This induces a Cantor-space homeomorphism by the standard infinite
prefix decoding argument, but NOT a uniform-measure-preserving map.
A literal FINITE orientable PL two-pants 1->3 cobordism is now built\nby exotic_topology_balanced_ternary_pl.py, with exact triangle/vertex-link\nand old-boundary dual-component audits. The INFINITE geometric end-space\nrealisation and kernel typechecks remain unproved.
"""
from itertools import product
from fractions import Fraction
import json

CODE={'3':'0','6':'10','9':'11'}

def encode(trits): return ''.join(CODE[t] for t in trits)

def decode(bits):
    i=0;out=[]
    while i < len(bits):
        if bits[i]=='0':out.append('3');i+=1
        elif i+1==len(bits): return None
        elif bits[i+1]=='0':out.append('6');i+=2
        else:out.append('9');i+=2
    return tuple(out)

def verify(depth=8):
    assert sorted(CODE.values())==['0','10','11']
    result={}
    for n in range(depth+1):
        families=list(product(CODE,repeat=n))
        codes=sorted(encode(t) for t in families)
        assert len(families)==3**n and len(codes)==len(set(codes))
        assert all(not b.startswith(a) for a,b in zip(codes,codes[1:])),n
        mass=sum((Fraction(1,2**len(c)) for c in codes),Fraction())
        assert mass==1,n
        assert all(decode(encode(t))==t for t in families)
        assert all(encode(decode(c))==c for c in codes)
        assert all(n<=len(c)<=2*n for c in codes)
        result[n]={'n_cylinders':len(codes),'dyadic_mass':str(mass),
                   'minimum_length':min(map(len,codes)),
                   'maximum_length':max(map(len,codes))}
    weights={k:Fraction(1,2**len(code)) for k,code in CODE.items()}
    assert sum(weights.values())==1
    assert any(x!=Fraction(1,3) for x in weights.values())
    assert weights['3']*weights['6']==Fraction(1,8)!=Fraction(1,9)
    return {'levels':result,'weights':{k:str(v) for k,v in weights.items()},
            'uniform_ternary_measure_preserved':False,
            'finite_prefix_codec_exact':True,
            'infinite_homeomorphism_kernel_verified':False,
            'pants_surface_realised':False}

if __name__=='__main__':
    print(json.dumps({'result':verify(),'status':'PASS prefix-free/Kraft/mass inequivalence'},indent=2,sort_keys=True))
