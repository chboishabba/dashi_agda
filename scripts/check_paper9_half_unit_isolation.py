#!/usr/bin/env python3
"""Exact signed half-unit root isolation regression on the original packet."""
from fractions import Fraction as F
from hashlib import sha1
from json import loads
from pathlib import Path
from sys import argv
import sympy as s

K=-640320**3
PACKET='17ed967d83d1aacafdb0f19d7bd81e6afc5887a4'
def shift(desc):
    out=[0]*len(desc)
    for x in desc:
        for i in range(len(out)-1,0,-1):
            out[i]=K*out[i]+out[i-1]
        out[0]=K*out[0]+x
    return out

def horner(x,cs):
    r=0
    for c in reversed(cs): r=c+x*r
    return r

def check(p):
    assert p[:2]==[0,0] and p[2]<0
    majorant=F(1,2)*horner(F(1,2),list(map(abs,p[3:])))
    assert majorant < -p[2]
    for i in range(-64,65):
        u=F(i,128)
        t=u*horner(u,p[3:])
        assert abs(t)<=majorant and p[2]+t<0
        assert horner(u,p)==u*u*(p[2]+t)
        assert (horner(u,p)==0)==(u==0)
    return majorant/F(-p[2])

u,p2,c3,c4,c5=s.symbols('u p2 c3 c4 c5')
assert s.expand(horner(u,[0,0,p2,c3,c4,c5])-u*u*(p2+u*horner(u,[c3,c4,c5])))==0
for p in [[0,0,-5,1,-2,3],[0,0,-1,0,0,1],[0,0,-9,-4,5,6]]: check(p)
print('SymPy',s.__version__,'1 symbolic factorization; 387 signed rational sample controls PASS')
if len(argv)>1:
    raw=Path(argv[1]).read_bytes()
    assert sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==PACKET
    p,q=(shift([int(c,16) for c in a]) for a in loads(raw))
    assert q[:2]==[0,0] and q[2]<0 and 41*p[2]==163*q[2]
    assert (41*p[3]-326*q[3])*19943834790540897829879824384000==-77859659565707*163*q[2]
    ratio=check(p)
    assert ratio<F(152,10**18)
    print('original packet: 80-term signed dominance; 129 rational sample controls PASS')
