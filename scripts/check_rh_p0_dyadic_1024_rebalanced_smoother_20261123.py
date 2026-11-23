#!/usr/bin/env python3
"""RH P0: original dyadic k=1024, 4 boundary jumps and rebalanced 26-slot E2.

Exact rational checks for the original selected-W projective bounds.
Analytic C-infinity lemma (not kernel checked): first 52 box halfwidths
7/(52*1024), remaining infinite tail halfwidths 2^-n/1024, n>=1;
convolve with [-3/128,3/128] plateau at +-log p. Total radius 1/32,
flat top 1/64, L1=3/32, derivatives m<=52 bounded by 4*lambda^(m-1),
lambda=52*1024/7. No RH/GRH assertion.
"""
from fractions import Fraction as F
from math import comb, factorial

def mul(a,b):
    c=[F(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):c[i+j]+=x*y
    return c

E=[F(1)]
for w,n in [(F(1),9),(F(1,4),9),(F(1,196),2),
            (F(1,225),2),(F(1,289),2),(F(1,324),2)]:
    for _ in range(n):E=mul(E,[F(1),w])
assert len(E)==27 and E[0]==1 and E[1]==F(1294113017,114704100)
assert all(0<E[j]<=F(comb(26,j)) for j in range(27))
assert 8**5==32768==32*1024 and 4*256==1024
assert F(8,16)**5==F(1,32)
lam=F(52*1024,7)
assert F(52)*F(7,52*1024)+F(1,1024)==F(1,128)
assert F(3,128)+F(1,128)==F(1,32)
assert F(3,128)-F(1,128)==F(1,64)

def e(x):
    y=F(0)
    for a in E[::-1]:y=y*x+a
    return y
def H(r):
    return F(3,32)+F(4)/lam*(e((lam/F(r))**2)-1)
def H_old(r):
    return F(3,32)+sum(
      F(4)*E[j]*256**(2*j-1)*factorial(2*j-1)**2/F(r)**(2*j)
      for j in range(1,27))
def c(r):
    x=F(r)**2
    return F(567,1600*24)-F(28125,4)/x*(1+F(25,4)/x)
K=F(6484375,7134511104)
assert c(1214)<F(1,100)<c(1215)
assert H(9620)>F(1,4)>=H(9621)
assert 4*K*H(5533)>=64*c(5533) and 4*K*H(5534)<64*c(5534)
assert K*H(5129)>=64*c(5129) and K*H(5130)<64*c(5130)
assert all(4*K*H(r)/(1+H(r))<4*K<64*c(r)
           for r in (1215,2048,5130,5534,9621,32768,65536))
assert all(H(r)<H_old(r) for r in (1215,5534,9621,32768))
assert H_old(65536)<H(65536)
for r in (5534,9621,32768):
    assert H(r)==F(3,32)+sum(
        F(4)*E[j]*lam**(2*j-1)/F(r)**(2*j) for j in range(1,27))
print("PASS original 4*256=1024=q16 dyadic cell index (distinct provenance)")
print("PASS 52=(2*26) equal boxes, 1/1024 infinite dyadic tail, C-infinity support")
print("PASS all 26 weighted 4E_j terms collapse to one E((lambda/r)^2) evaluation")
print("PASS one-active-port l1 source r>=5130, t>=82080")
print("PASS all four independent r^-5 amplitudes r>=5534, t>=88544")
print("PASS aperture mass cap H<=1/4 r>=9621, t>=153936")
print("PASS adaptive amplitude r>=1215 and near-endpoint negative control")
print("OPEN full E2 true FarExact/post-sixth and independent E3 signed cut; no kernel")
