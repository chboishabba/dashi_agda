#!/usr/bin/env python3
"""Original P3^9 U(pi), 512 signed corners, C3^9 dual frequency charts.

Exact finite sourced programme: Base369Ternary27HypervoxelFabricGeometryExact,
Base369PeriodicTernaryTorusPathRestrictionBidiExact, original
check_hyperfabric_path27_quantum_walk.py U(pi), Griess/Sah grade G=-M.
Full chart equality and source sign provenance, NOT physical graph motion,
NS continuum, Yang-Mills Wilson equality or RH zeta-zero operator.
"""
from itertools import product
from fractions import Fraction as F
from math import comb
import sympy as s

T=(-1,0,1);V=tuple(product(T,repeat=3))
G=s.Matrix([[-1,-1,0],[0,-1,-1],[-1,-1,-1]])
Gi=G.inv_mod(3)
def balance(n):return (int(n)+1)%3-1
def chart(m):
    return {v:tuple(balance(z) for z in m*s.Matrix(v)) for v in V}
maps=[];backs=[];duals=[];dualinvs=[]
for k in range(27):
    maps.append(chart((G**k).applyfunc(lambda n:n%3)))
    backs.append(chart((Gi**k).applyfunc(lambda n:n%3)))
    duals.append(chart((Gi.T**k).applyfunc(lambda n:n%3)))
    dualinvs.append(chart((G.T**k).applyfunc(lambda n:n%3)))
def apply(v,table):
    return table[v[:3]]+table[v[3:6]]+table[v[6:]]
def position(v,k):return apply(v,maps[k%26])
def frequency(v,k):return apply(v,duals[k%26])
def inverse_position(v,k):return apply(v,backs[k%26])
def inverse_frequency(v,k):return apply(v,dualinvs[k%26])
corners=tuple(product((-1,1),repeat=9))
assert len(corners)==512 and 3**9==19683
zero_counts=[]
for k in range(26):
    ps={position(c,k) for c in corners}
    qs={frequency(c,k) for c in corners}
    assert len(ps)==len(qs)==512
    assert all(inverse_position(p,k) in corners for p in ps)
    assert all(inverse_frequency(q,k) in corners for q in qs)
    for c in corners:
        p=position(c,k);q=frequency(c,k)
        assert inverse_position(p,k)==inverse_frequency(q,k)==c
        assert position(c,k+1)==apply(p,maps[1])
        assert frequency(c,k+1)==apply(q,duals[1])
    for c in (corners[0],corners[1],corners[127],corners[511]):
        p=position(c,k);q=frequency(c,k)
        assert sum(a*b for a,b in zip(p,q))%3 == sum(x*x for x in c)%3
    zero_counts.append(sum(0 in position(c,k) for c in corners))
assert zero_counts[0]==0 and max(zero_counts)==512
assert zero_counts[13]==0
assert tuple(comb(9,r)*2**r for r in range(10))==(
 1,18,144,672,2016,4032,5376,4608,2304,512)
# The REAL source U(pi) on each P3 has B=2J/3-I; ninefold
# Kronecker gives the REAL original P3^9 path-walk U9(pi).
def b(a,c):return F(2,3)-int(a==c)
def amp(p,q):
    value=F(1)
    for a,c in zip(p,q):value*=b(a,c)
    return value
origin=(0,)*9
assert all(amp(c,origin)==F(512,19683) for c in corners)
assert amp(origin,origin)==-F(1,19683)
assert all(sum((b(x,a)*b(x,c) for x in T),F(0))==(1 if a==c else 0)
           for a in T for c in T)
for k in range(26):
    assert all(amp(inverse_position(position(c,k),k),origin)==F(512,19683)
               for c in corners)
print("PASS original 9D source U9(pi)=B tensor nine, rational orthogonal, 512/19683 corner amplitude")
print("PASS 26 signed k-stage 512/512 original-corner dual Fourier chart bijections")
print("PASS position G and contragredient frequency G^-T commute with true index transport")
print("PASS reference sign/zero masks recover while current chart zeros appear:",zero_counts)
print("OPEN physical graph deformation, full NS Fourier dynamics, YM Wilson, RH FarExact")
