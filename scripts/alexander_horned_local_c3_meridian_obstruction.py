#!/usr/bin/env python3
"""Exact free-group audit. Does not certify any 3D geometry or Agda source."""
def red(w):
    s=[]
    for x in w:
        if s and s[-1]==-x:s.pop()
        else:s.append(x)
    return tuple(s)
def inv(w):return tuple(-x for x in reversed(w))
def comm(x,y):return red(tuple(x)+tuple(y)+inv(x)+inv(y))
def cyc(w):
    w=list(red(w))
    while len(w)>1 and w[0]==-w[-1]:w=w[1:-1]
    return tuple(w)
def conjugate(x,y):
    x,y=cyc(x),cyc(y)
    return any(x==y[k:]+y[:k] for k in range(len(y))) if y else x==()
def rotate(w):
    r={1:2,2:3,3:1}
    return red(tuple((1 if x>0 else -1)*r[abs(x)] for x in w))
a,b,c=(1,),(2,),(3,)
w=red(comm(a,b)+comm(b,c))
rw=rotate(w)
assert w==(1,2,-1,3,-2,-3)
assert rw==(2,3,-2,1,-3,-1)
assert rotate(rotate(rotate(w)))==w
assert not conjugate(rw,w)
assert not conjugate(rw,inv(w))
print("PASS: local C3 rotates the ternary bonding word outside its conjugacy and inverse-conjugacy classes")
print("Scope: parent meridian fixed up to conjugacy (and optionally inversion), and children cyclically permuted.")
print("Does not obstruct external C3 permuting three separate whole-root sectors.")
