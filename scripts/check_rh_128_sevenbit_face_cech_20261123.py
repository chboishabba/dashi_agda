#!/usr/bin/env python3
"""Exhaustive source-derived RH 128 seven-bit six-face Cech test.

Owners: Lean quarticFour FourierMass/NMu; DASHI Base369Ternary27BoundaryNerve,
ActualFaceHypercubeGluingFromSharedSlice, TernaryThirteenPantsSheaf.
This models EXACT normalization coefficient labels, not a ζ/Monster actor.
"""
from fractions import Fraction as F
from itertools import product, combinations
from collections import Counter
import sympy as s
import mpmath as mp

states=list(product((0,1),repeat=7))
faces=[(i,j) for i in range(3) for j in (0,1)]
edges=[(i,x,j,y) for i,j in combinations(range(3),2)
       for x,y in product((0,1),repeat=2)]
corners=list(product((0,1),repeat=3))
axes=(0,4,5); rest=(1,2,3,6)
gauges={f:F(2)**(k-2) for k,f in enumerate(faces)}
def corner(b):return tuple(b[i] for i in axes)
def residual(b):return tuple(b[i] for i in rest)
def join(c,r):
    b=[0]*7
    for i,x in zip(axes,c): b[i]=x
    for i,x in zip(rest,r): b[i]=x
    return tuple(b)
def blocks(b):return (2**sum(b[:4]),2**b[4],2**sum(b[5:]))
def weight(b):return 2**sum(b)
def belongs(b,f):return corner(b)[f[0]]==f[1]
def at(b,f,sign):return F(weight(b)*sign)/gauges[f]
def transport(v,f,g):return v*gauges[f]/gauges[g]

assert len(states)==128 and len(faces)==6 and len(edges)==12 and len(corners)==8
assert blocks((1,)*7)==(16,2,4) and weight((1,)*7)==128
assert Counter(map(corner,states))==Counter({c:16 for c in corners})
for b in states:
    assert join(corner(b),residual(b))==b
    a,m,c=blocks(b); assert weight(b)==a*m*c
    assert sum(belongs(b,f) for f in faces)==3
assert all(sum(belongs(b,f) for b in states)==64 for f in faces)
assert all(sum(belongs(b,e[:2]) and belongs(b,e[2:]) for b in states)==32 for e in edges)
print("PASS 128=8 actual geometric corners x 16 retained residual; 6 faces x64, 12 edges x32, 8 corners x16")

face_tests=edge_tests=cocycle_tests=0
for sign in (-1,0,1):  # independent sign and zero retain exact scalar multiplication
    for b in states:
        incident=[f for f in faces if belongs(b,f)]
        global_value=weight(b)*sign
        assert all(gauges[f]*at(b,f,sign)==global_value for f in incident)
        face_tests+=len(incident)
    for e in edges:
        f,g=e[:2],e[2:]
        for b in states:
            if belongs(b,f) and belongs(b,g):
                assert transport(at(b,f,sign),f,g)==at(b,g,sign)
                assert transport(transport(at(b,f,sign),f,g),g,f)==at(b,f,sign)
                edge_tests+=1
    for c in corners:
        f,g,h=[(i,c[i]) for i in range(3)]
        for b in states:
            if corner(b)==c:
                assert transport(at(b,f,sign),f,h)==transport(transport(at(b,f,sign),f,g),g,h)
                cocycle_tests+=1
assert (face_tests,edge_tests,cocycle_tests)==(1152,1152,384)
print("PASS 1152 signed/zero face restrictions; 1152 reversible edge transports; 384 3-face corner cocycles")

b=(0,)*7; f=(0,0); g=(1,0)
assert transport(at(b,f,1)+F(1,4),f,g)!=at(b,g,1)
assert len({residual(x) for x in states if corner(x)==(0,0,0)})==16
print("PASS adversarial bad gluing rejected; projection to 8 corners without 16-fibre is noninjective")

t,R,M,O,N=s.symbols("t R M O N",positive=True)
assert s.simplify((16/t)*(2*s.pi)*(4*O/(R*M))-128*s.pi*O/(t*R*M))==0
assert s.simplify((4/(s.pi*t))*(-s.Rational(1,256))*(-2*s.pi)-1/(32*t))==0
assert s.simplify((s.log(N)/(2*s.pi))*(128*s.pi*O/(t*R*M))-
                  64*s.log(N)*O/(t*R*M))==0
assert 768==3*16**2 and 800==80*10==2**5*5**2==100*(9-1)
q=s.symbols("q",positive=True)
assert s.integrate(2*q**(-4),(q,8,s.oo))==s.Rational(1,768)
assert s.simplify(800-s.log(9-1))!=0
print("PASS 32*t / 64 log N / 800 and 768 coefficients source chain; reject 800=log(9-1)")

mp.mp.dps=40
def mu(x):
    return (mp.re(mp.digamma(mp.mpf("0.25")+mp.j*x/2))-mp.log(mp.pi))/(2*mp.pi)
def delta(q):
    T=mp.mpf(200)
    return mu(T*(1+mp.mpf(q)/16))+mu(T*(1-mp.mpf(q)/16))-2*mu(T)
qprobes=(2,8,12,20,24,32)
vals=dict(zip(faces,map(delta,qprobes)))
assert len(set(round(float(x),12) for x in vals.values()))==6
assert all(abs(vals[e[:2]]-vals[e[2:]])>mp.mpf("1e-12") for e in edges)
print("PASS negative control: 6 Fourier probes DO NOT glue as 6 cube-face values (12/12 mismatches)")
print("OPEN actual original selected-W / paperFT same-analytic-source, zero-side and Monster action intertwiner")


# Native existing Monster3B X6 = F3^6 and SignedSSPFRACTRAN C2.
# Bit->trit sends 0->-1, 1->+1; seventh bit is signed SSP unit.
# Exact injected C2 action on EXISTING finite carriers, NOT a Monster group
# action on original RH W / zero set.
def monster_ssp_image(bits):
    return tuple((1 if x else -1)%3 for x in bits[:6]),(1 if bits[6] else -1)
def monster_ssp_inverse(img):
    six,sign=img
    assert all(x in (1,2) for x in six) and sign in (-1,1)
    return tuple(int(x==1) for x in six)+(int(sign==1),)
def signed_c2(img):
    six,sign=img
    return tuple((-x)%3 for x in six),-sign

images={monster_ssp_image(bits) for bits in states}
assert len(images)==128
for bits in states:
    image=monster_ssp_image(bits)
    assert monster_ssp_inverse(image)==bits
    flipped=tuple(1-x for x in bits)
    assert monster_ssp_image(flipped)==signed_c2(image)
    assert weight(bits)*weight(flipped)==128
assert signed_c2(((0,)*6,0))==((0,)*6,0)
assert ((0,)*6,0) not in images
print("PASS 128/128 native F3^6 x signed-SSP BIDI, actual C2 and complement-weight reciprocity")
print("PASS ternary neutral fixed point OUTSIDE nonzero binary image; no Monster group / RH source action")
