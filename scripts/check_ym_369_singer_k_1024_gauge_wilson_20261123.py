#!/usr/bin/env python3
"""Original Singer G^k charts on actual 4D YM 1024-link gauge-fibred field.

Uses the source G from RH #1533 on three blocks of the nine-trit address.
The incidence graph MUST be transported together with the chart;
G need not preserve the fixed P3^9 nearest-neighbour adjacency.
Finite Q8 SU2-subgroup original Wilson geometry only, not physical YM k flow.
"""
from collections import defaultdict
from itertools import product
import sympy as s
from check_ym_369_original_full1024_wilson_gauge_fibre_20261123 import (
    sites,coarse_bonds,original_bonds,original_plaquettes,
    pair,step,sign9,gauge,field,transformed,plaquette,word_value,mul,inv
)

G=s.Matrix([[-1,-1,0],[0,-1,-1],[-1,-1,-1]])
Gi=G.inv_mod(3)
def bal(x):return (int(x)+1)%3-1
def chart9(vec,m):
    return tuple(z for i in range(0,9,3)
                 for z in (bal(x) for x in m*s.Matrix(vec[i:i+3])))

orig_sgn={site:sign9(site) for site in sites}
# Branch records are indexed by zeros at SOURCE k=0, NOT new current
# zero positions that appear after non-diagonal Singer transport.
def source_branch(site):
    return tuple(None if v%2==0 else (v-1)//2 for v in site)
def decode_source(p0, branch):
    assert p0[4:]==(0,)*5
    return tuple(0 if x==-1 else 2 if x==1 else 1+2*b
                 for x,b in zip(p0[:4],branch))
assert all(decode_source(orig_sgn[x],source_branch(x))==x for x in sites)

trace=lambda q: 1 if q==0 else -1 if q==4 else 0
counts=[]
for k in range(26):
    M=(G**k).applyfunc(lambda x:int(x)%3)
    B=(Gi**k).applyfunc(lambda x:int(x)%3)
    p={site:chart9(orig_sgn[site],M) for site in sites}
    assert len(set(p.values()))==81
    assert all(chart9(p[site],B)==orig_sgn[site] for site in sites)
    assert all(decode_source(chart9(p[site],B),source_branch(site))==site
               for site in sites)
    def vertex(site):return k,p[site],source_branch(site)
    def label(b):
        site,axis=b
        return vertex(site),vertex(step(site,axis)),axis
    lifted={label(b):field[b] for b in original_bonds}
    gauged={label(b):transformed[b] for b in original_bonds}
    assert len(lifted)==len(gauged)==1024
    assert len({vertex(site) for site in sites})==256
    for bond in original_bonds:
        site,axis=bond
        assert gauged[label(bond)]==mul(
            mul(gauge(site),lifted[label(bond)]),inv(gauge(step(site,axis))))
    # All original 1536 Wilson plaquette words remain the same GROUP
    # elements on the transported labelled incidence graph.
    for site,mu,nu in original_plaquettes:
        word=plaquette(site,mu,nu)
        actual=word_value(word,field)
        transported=word_value(word,{(x,d):lifted[label((x,d))]
                                     for x,d,_ in word})
        gauge_actual=word_value(word,transformed)
        gauge_transported=word_value(word,{(x,d):gauged[label((x,d))]
                                           for x,d,_ in word})
        assert actual==transported
        assert gauge_actual==gauge_transported
        assert trace(gauge_actual)==trace(actual)
    # A fixed P3 edge changes ONE coordinate by exactly one.
    neighbour=lambda x,y:sum(abs(a-b) for a,b in zip(x,y))==1
    selected=[(pair(c,d)[0],pair(c,d)[1]) for c,d in coarse_bonds]
    direct_count=sum(neighbour(p[u[0]],p[v[0]]) for u,v in selected)+sum(
        neighbour(p[v[0]],p[step(v[0],d)])
        for c,d in coarse_bonds for u,v in [pair(c,d)])
    counts.append(direct_count)
assert counts[0]==128
assert any(c<128 for c in counts[1:])
print('PASS 26/26 original Singer G^k charts and inverse with source-zero branches')
print('PASS 26 x 1024 = 26624 original group-link and local-gauge checks')
print('PASS 26 x 1536 = 39936 original Wilson plaquette and gauged trace checks')
print('P3^9 FIXED-edge survival across source Singer stages:',counts)
print('PASS fixed P3^9 adjacency not preserved; transport ORIGINAL incidence graph')
print('LIMIT chart transport ONLY; not physical YM k dynamics, CMP119 T or W3 decay')
