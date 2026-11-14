#!/usr/bin/env python3
"""Exact integer-matrix certificate of point group 4/mmm = D4h.

Computational certificate, not an Agda/Lean kernel proof or physical specimen
identification. Mirrors and twofold axes counted as distinct group operations.
"""
from itertools import product
I=((1,0,0),(0,1,0),(0,0,1))
R=((0,-1,0),(1,0,0),(0,0,1))
S=((1,0,0),(0,-1,0),(0,0,1))
H=((1,0,0),(0,1,0),(0,0,-1))
def mul(a,b):
    return tuple(tuple(sum(a[i][k]*b[k][j] for k in range(3))
                 for j in range(3)) for i in range(3))
def power(a,n):
    v=I
    for _ in range(n): v=mul(v,a)
    return v
def det(a):
    return (a[0][0]*(a[1][1]*a[2][2]-a[1][2]*a[2][1])
           -a[0][1]*(a[1][0]*a[2][2]-a[1][2]*a[2][0])
           +a[0][2]*(a[1][0]*a[2][1]-a[1][1]*a[2][0]))
def trace(a): return sum(a[i][i] for i in range(3))
def act(a,p):
    return tuple(sum(a[i][j]*p[j] for j in range(3)) for i in range(3))
def invariants(p):
    x,y,z=p
    return x*x+y*y, x*x*y*y, z*z
def verify():
    assert power(R,4)==I and power(S,2)==I and power(H,2)==I
    assert mul(mul(S,R),S)==power(R,3)
    assert mul(H,R)==mul(R,H) and mul(H,S)==mul(S,H)
    elems={mul(mul(power(R,a),power(S,b)),power(H,c))
           for a,b,c in product(range(4),range(2),range(2))}
    assert len(elems)==16
    assert all(mul(a,b) in elems for a in elems for b in elems)
    assert sum(det(a)==1 for a in elems)==8
    assert sum(det(a)==-1 for a in elems)==8
    negI=tuple(tuple(-x for x in row) for row in I)
    assert mul(power(R,2),H)==negI
    assert mul(negI,R) in elems
    c2=[a for a in elems if det(a)==1 and a!=I and
        mul(a,a)==I and trace(a)==-1]
    mirrors=[a for a in elems if det(a)==-1 and
             mul(a,a)==I and trace(a)==1]
    assert len(c2)==5 and power(R,2) in c2
    assert len(mirrors)==5 and H in mirrors
    assert all(invariants(act(a,p))==invariants(p)
               for a in elems for p in product(range(-2,3),repeat=3))
    print("PASS: 4/mmm, 16 operations; 8 proper/8 improper; 5 C2 axes; 5 mirrors.")
if __name__=="__main__": verify()
