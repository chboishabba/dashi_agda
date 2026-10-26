#!/usr/bin/env python3
"""Exhaustive independent orbit check for the actual pointed 10 x 3^9 sheet.

D4 quarter/mirror moves the marked site; global value S3 permutes all nine
trits. This verifies the 4396 pointed orbits without Burnside or character
formulas. Source: PointedTernaryBulkExact and IITJFineFourOneFourS3ZetaGaugeExact.
"""
from __future__ import annotations
import json

N=3**9
R=(6,3,0,7,4,1,8,5,2)
S=(2,1,0,5,4,3,8,7,6)

def decode(n):
    out=[]
    for _ in range(9):
        out.append(n%3)
        n//=3
    return out

def encode(vals):
    n=0
    for v in vals[::-1]:
        n=3*n+v
    return n

def site_transform(p):
    return [encode([x[p[i]] for i in range(9)])
            for x in map(decode,range(N))]

def marker_map(p):
    return [0]+[1+p.index(i) for i in range(9)]

def audit():
    rot=site_transform(R)
    mirror=site_transform(S)
    translation=[encode([(x+1)%3 for x in decode(n)]) for n in range(N)]
    sign=[encode([(-x)%3 for x in decode(n)]) for n in range(N)]
    actions=((rot,marker_map(R)),(mirror,marker_map(S)),
             (translation,list(range(10))),(sign,list(range(10))))
    assert marker_map(R)[1]==3  # NW -> NE
    visited=bytearray(10*N)
    histogram={}
    orbits=0
    for origin in range(10*N):
        if visited[origin]:
            continue
        orbits+=1
        visited[origin]=1
        stack=[origin]
        size=0
        while stack:
            x=stack.pop()
            size+=1
            sheet,marker=divmod(x,10)
            for tr,marked in actions:
                y=10*tr[sheet]+marked[marker]
                if not visited[y]:
                    visited[y]=1
                    stack.append(y)
        histogram[size]=histogram.get(size,0)+1
    assert orbits==4396
    assert histogram=={3:2,6:12,12:36,24:512,48:3834}
    assert sum(k*v for k,v in histogram.items())==196830
    return {
        "scope":"finite source actual pointed D4 x value-S3, not Monster action",
        "states_visited":sum(visited),
        "orbits":orbits,
        "orbit_sizes":dict(sorted(histogram.items())),
        "moving_marker":True,
        "does_not_equal_ten_inert_copies":orbits!=10*490,
        "Agda_kernel_verification":False
    }

if __name__=="__main__":
    print(json.dumps(audit(),indent=2,sort_keys=True))
