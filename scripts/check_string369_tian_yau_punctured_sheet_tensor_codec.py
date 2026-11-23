#!/usr/bin/env python3
"""Exact mean/residual three-punctured-sheet representation and tensor codec.

Classical: finite-group representations, Reynolds projection, radix
division and rational arithmetic. Original DASHI: Punctured27NineSheetBridge,
TriadicPAdicCodec, TriadicVideoCodecObservationQuotient, original selected
Tian-Yau Jacobian cubic, T18 and E6 first-Tits. User: three punctured sheets,
modulo 101 and codec. New: constructive rational intertwiner plus lossless
coefficient orbit encoding. Not native geometric sheet permutation,
geometric residue comparison, physical Yukawa normalization or MDL optimum.
"""
from pathlib import Path
from itertools import combinations_with_replacement
from math import gcd,lcm
import runpy
import sympy as s

# Use exactly the previous source, including its independent rank checks.
d=runpy.run_path(str(Path(__file__).with_name(
    'check_string369_tian_yau_jacobian_cubic_exact.py')))
P,P2,S,K,B,T,R=(d[k] for k in ('P','P2','S','K','B','T','R'))
n=23
# 3 sheets of 8 punctured positions, each split into mean and 7
# zero-sum directions. No individual position is declared the centre.
one=s.ones(8,1)
D=s.Matrix.hstack(one,*[s.eye(8)[:,j]-s.eye(8)[:,7] for j in range(7)])
assert D.det()!=0 and one.T*D[:,1:]==s.zeros(1,7)
# Coordinates sorted as seven residual triples, then three means.
L=s.zeros(24)
for j in range(7):
    for k in range(3):
        L[8*k:8*k+8,3*j+k]=D[:,j+1]
for k in range(3):
    L[8*k:8*k+8,21+k]=one
A=s.diag(*([R]*7),s.eye(3))
G=L*A*L.inv()
assert G**3==s.eye(24) and G.trace()==3
for k in range(3):
    assert G*L[:,21+k]==L[:,21+k]
# Construct actual intertwiner to R2, placing the known radical first
# among three fixed coordinate directions.
cols=[]
for j in range(24):
    e=s.eye(24)[:,j]
    trial=cols+[e,P2*e,P2**2*e]
    if s.Matrix.hstack(*trial).rank()==len(trial):cols=trial
    if len(cols)==21:break
assert len(cols)==21
cols.append(K[0])
assert s.Matrix.hstack(*cols).rank()==22
for e in (s.eye(24)+P2+P2**2).columnspace():
    if s.Matrix.hstack(*(cols+[e])).rank()==len(cols)+1:cols.append(e)
assert len(cols)==24
S2=s.Matrix.hstack(*cols)
assert P2*S2==S2*A
J=S2*L.inv()
assert P2*J==J*G and J*L[:,21]==K[0]
assert B*S2[:,21]==s.zeros(23,1)
assert (B*S2[:,list(range(21))+[22,23]]).rank()==23
# Mod-101 centered digit + quotient. Five native balanced trits per
# digit; no claim that a 101 digit is a full 243-state trit word.
def pack5(r):
    value=0
    for i in range(5):
        t=(r+1)%3-1
        value+=(t+1)*3**i
        r=(r-t)//3
    assert r==0
    return value
def unpack5(b):
    assert 0<=b<243
    return sum(((b//3**i)%3-1)*3**i for i in range(5))
def encode_int(a):
    out=[]
    while a:
        r=(a+50)%101-50
        out.append(pack5(r))
        a=(a-r)//101
    return tuple(out)
def decode_int(out):
    ds=[unpack5(b) for b in out]
    assert all(-50<=r<=50 for r in ds)
    return sum(r*101**i for i,r in enumerate(ds))
for a in range(-10000,10001):
    assert decode_int(encode_int(a))==a
def encode_q(q):
    a,b=map(int,s.fraction(s.Rational(q)))
    return encode_int(a),encode_int(b)
def decode_q(p):
    a,b=map(decode_int,p)
    assert b>0 and gcd(a,b)==1
    return s.Rational(a,b)
# Transform actual cubic into permutation coordinates; then use
# symmetric triples and cyclic orbit representatives (not merely
# assuming orbit coefficients agree in the old non-permutation basis).
TT=[]
for i in range(n):
    H=sum((S[j,i]*T[j] for j in range(n)),s.zeros(n))
    TT.append(S.T*H*S)
def phase(i):return 3*(i//3)+(i+1)%3 if i<21 else i
def orbit(t):
    return {tuple(sorted(t)),tuple(sorted(map(phase,t))),
            tuple(sorted(phase(phase(i)) for i in t))}
triples=list(combinations_with_replacement(range(n),3))
reps={min(orbit(t)) for t in triples}
assert len(reps)==774 # Burnside: (2300 + 2*(7+4))/3
# Store nonzero orbit entries; zeros are implicit under a specified
# support map. Not a claimed compressed byte count.
payload={}
for t in reps:
    i,j,k=t;q=TT[i][j,k]
    assert all(TT[a][b,c]==q for a,b,c in orbit(t))
    if q:payload[t]=encode_q(q)
def read(i,j,k):
    p=payload.get(min(orbit((i,j,k))))
    return decode_q(p) if p is not None else s.S.Zero
for i in range(n):
    for j in range(n):
        for k in range(n):assert read(i,j,k)==TT[i][j,k]
# Decode all transformed slices, then invert change of basis.
inv=S.inv()
decoded=[s.Matrix(n,n,lambda j,k:read(i,j,k)) for i in range(n)]
back=[inv.T*sum((inv[j,i]*decoded[j] for j in range(n)),s.zeros(n))*inv
      for i in range(n)]
assert back==T
# Also preserve the literal degree 1 x degree 1 -> degree 2 map
# and degree 1 x degree 2 -> degree 3 pairing, including radical.
m1,f1,m2,r2,idx2=(d[k] for k in ('m1','f1','m2','r2','idx2'))
for i,j in combinations_with_replacement(range(n),2):
    m=tuple(a+b for a,b in zip(m1[f1[i]],m1[f1[j]]))
    raw=s.Matrix(r2[idx2[m]])
    recovered=s.Matrix([decode_q(encode_q(q)) for q in raw])
    assert recovered==raw
    assert B*recovered==T[i][:,j]
assert B.applyfunc(lambda q:decode_q(encode_q(q)))==B
print('PASS mean-preserving punctured sheets: 24 -> radical quotient 23')
print('PASS explicit R2 intertwiner and perfect quotient pairing')
print('PASS modulo-101 centered digit and five-trit reconstruction')
print('PASS cubic orbit representatives',len(reps),'nonzero',len(payload))
print('PASS all 23^3 cubic entries and inverse basis transport')
print('PASS raw degree-one products and degree-two pairing')
print('OPEN native sheet chart transport; geometric residue and normalized physics')
