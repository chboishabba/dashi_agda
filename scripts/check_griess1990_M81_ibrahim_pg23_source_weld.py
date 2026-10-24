#!/usr/bin/env python3
"""Agda-side independent source-donor reuse: Griess 1990 M81/PG(2,3).

REUSES the existing Agda #1239 independent Griess source-to-native
certificate verifier and its original F3^3 phase polynomial. The #1249
original fixture is on a separate PR branch and is NOT imported here.

Original external source: Robert L. Griess Jr., Journal of Algebra 131
(1990) 281–293, DOI 10.1016/0021-8693(90)90176-O.
Ibrahim/OEIS 13 is numerically the same cardinality but is not a
proof identifying the physical cube graph with projective incidence.
Monster Vsharp, F4/E6 and physical claims remain distinct.
"""
from pathlib import Path
from itertools import product,combinations
from collections import Counter
import runpy
prior=runpy.run_path(str(Path(__file__).with_name(
    'check_griess1990_rational_triality_crossprover_certificate.py')))
V=prior['V']; g=prior['phase']; add=prior['add']; neg=prior['neg']
origin=(0,0,0)
assert len(V)==27
def det(x,y,z):
    a,b,c=x;p,q,r=y;u,v,w=z
    return (a*(q*w-r*v)-b*(p*w-r*u)+c*(p*v-q*u))%3
def mul(x,y):
    return add(x[0],y[0]),(x[1]+y[1]+g(x[0],y[0]))%3
M=tuple(product(V,range(3))); e=(origin,0)
assert len(M)==81
assert all(mul(e,x)==x and mul(x,e)==x and mul(mul(x,x),x)==e
           for x in M)
assert all(mul(x,y)==mul(y,x) for x,y in product(M,repeat=2))
classes=Counter()
for x,y,z in product(V,repeat=3):
    d=(g(x,y)+g(add(x,y),z)-g(y,z)-g(x,add(y,z)))%3
    assert d==det(x,y,z)
    classes[d]+=1
    a,b,c=(x,0),(y,0),(z,0)
    assert mul(mul(a,b),mul(c,a))==mul(a,mul(mul(b,c),a))
assert classes=={0:8451,1:5616,2:5616}
L=tuple(x for x in V if x!=origin and x<neg(x))
assert len(L)==13
def inc(x,y):return sum(a*b for a,b in zip(x,y))%3==0
assert sum(inc(x,y) for x,y in product(L,repeat=2))==52
assert all(sum(inc(x,y) for y in L)==4 for x in L)
assert all(sum(inc(x,y) for x in L)==4 for y in L)
assert all(sum(inc(x,z) and inc(y,z) for z in L)==1
           for x,y in combinations(L,2))
col=sum(det(x,y,z)==0 for x,y,z in combinations(L,3))
assert col==52 and 286-col==234
assert all((det(x,y,z)==0)==any(inc(x,n) and inc(y,n) and inc(z,n)
           for n in L) for x,y,z in combinations(L,3))
print('PASS independent Agda source fixture: 81 Griess Moufang elements')
print('PASS all 19683 associators δg=det, class counts 8451/5616/5616')
print('PASS PG(2,3) 13 grade-antipodal lines, 52 incidences, 78 point pairs')
print('NO promotion to Monster Vnatural modes, physical P3^3 edges or exceptional Lie group actions')
