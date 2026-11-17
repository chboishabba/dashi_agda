#!/usr/bin/env python3
"""Native C3 x balanced-ternary infinite ends: exact finite test.

Uses classical complete prefix code {-:0,0:10,+:11} already owned by
stacked exotic PR #1254, and the existing DASHI tetration count.
This is a TAME Euclidean comparator, NOT the Alexander wild embedding.
"""
from fractions import Fraction as F
from itertools import product
import json

TRITS=(-1,0,1)
CODE={-1:(0,),0:(1,0),1:(1,1)}

def encode(ts):
    return tuple(b for t in ts for b in CODE[t])

def decode(bs):
    out=[];i=0
    while i<len(bs):
        if bs[i]==0:out.append(-1);i+=1
        elif i+1<len(bs):out.append(0 if bs[i+1]==0 else 1);i+=2
        else:return tuple(out),True
    return tuple(out),False

def ball(w):
    # Three internally separated base-7 branches in [1/6,1/2].
    n=len(w);L=F(1,3*7**n)
    lo=F(1,6)+F(1,3)*sum(
        (F(3*(t+1),7**(j+1)) for j,t in enumerate(w)),F(0))
    return (lo+L/2,F(1,2),F(0)),F(3,5)*L

def check(max_depth=7):
    total=0
    for n in range(max_depth+1):
        words=list(product(TRITS,repeat=n))
        assert len(words)==3**n
        assert len({encode(w) for w in words})==len(words)
        for w in words:
            out,pending=decode(encode(w))
            assert not pending and out==w
            parent,r=ball(w)
            assert r==F(1,5*7**n)
            children=[ball(w+(t,)) for t in TRITS]
            assert all(abs(child[0]-parent[0])+cr<r for child,cr in children)
            assert all(children[i+1][0][0]-children[i][0][0]>
                       children[i][1]+children[i+1][1] for i in range(2))
            assert all(encode(w+(t,))[:len(encode(w))]==encode(w)
                       for t in TRITS)
            total+=1
    for n in range(13):
        for bits in product((0,1),repeat=n):
            out,pending=decode(bits)
            assert encode(out)==bits[:len(encode(out))]
            assert pending==(len(bits)>len(encode(out)))
            if pending:assert bits[-1]==1

    # Complete prefix code: 1/2+1/4+1/4=1.
    # Fair binary source induces nonuniform iid trits; uniform trits
    # do NOT correspond to fair binary cylinder probability.
    assert sum(F(1,2)**len(CODE[t]) for t in TRITS)==1
    assert [F(1,2)**len(CODE[t]) for t in TRITS]==[
        F(1,2),F(1,4),F(1,4)]
    assert F(1,3)!=F(1,2)

    cells=[3*3**n for n in range(6)]
    assert cells==[3,9,27,81,243,729]
    assert 3**cells[2]==3**27==7625597484987
    root,r=ball(())
    assert root==(F(1,3),F(1,2),F(0)) and r==F(1,5)
    assert (root[0]+r)**2+(root[1]+r)**2+r*r<1

    return {'status':'PASS','three_sectors':3,
      'balanced_prefixes_by_depth':cells,
      'prefixes_checked':total,'sector_prefixes_checked':3*total,
      'binary_prefixes_checked':sum(2**n for n in range(13)),
      'depth2_balanced_cells':27,
      'depth2_trit_configuration_count':3**27,
      'prefix_code':{'-1':'0','0':'10','+1':'11'},
      'uniform_trit_first_binary_zero':'1/3',
      'fair_binary_trit_weights':['1/2','1/4','1/4'],
      'limit_homeomorphism':'all-depth prefix-code argument, not kernel verified',
      'embedding':'explicit tame base-7 comparator; NOT wild horns'}

if __name__=='__main__':
    print(json.dumps(check(),indent=2))
