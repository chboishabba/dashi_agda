#!/usr/bin/env python3
from fractions import Fraction as F
from itertools import combinations

# Exact-rational recovery of
#   Der(H_3(O_Q)) = tri(O_Q) + O_Q + O_Q + O_Q
# with dimensions 28 + 8 + 8 + 8 = 52.
#
# The octonion triality algebra is solved as triples (A,B,C) in so(8)^3 with
#   A(xy) = B(x)y + x C(y).
# Under the Albert coordinate convention the induced block derivation is
#   x-block: conjugation o A o conjugation,
#   y-block: B,
#   z-block: C.

Z8=(F(0),)*8

def qmul(a,b):
    a0,a1,a2,a3=a; b0,b1,b2,b3=b
    return (a0*b0-a1*b1-a2*b2-a3*b3,
            a0*b1+a1*b0+a2*b3-a3*b2,
            a0*b2-a1*b3+a2*b0+a3*b1,
            a0*b3+a1*b2-a2*b1+a3*b0)
def qconj(a): return (a[0],-a[1],-a[2],-a[3])
def omul(x,y):
    a,b=x[:4],x[4:]; c,d=y[:4],y[4:]
    ac=qmul(a,c); cdb=qmul(qconj(d),b)
    da=qmul(d,a); bc=qmul(b,qconj(c))
    return tuple(ac[i]-cdb[i] for i in range(4))+tuple(da[i]+bc[i] for i in range(4))
def oconj(x): return (x[0],)+tuple(-u for u in x[1:])
def oscale(c,x): return tuple(c*u for u in x)
def inner(x,y): return omul(x,oconj(y))[0]
def unpack(v): return v[0],v[1],v[2],tuple(v[3:11]),tuple(v[11:19]),tuple(v[19:27])
def pack(a,b,c,x,y,z): return (a,b,c)+tuple(x)+tuple(y)+tuple(z)
def sum8(ts): return tuple(sum(t[k] for t in ts) for k in range(8))

def jprod(A,B):
    a,b,c,x,y,z=unpack(A); ap,bp,cp,xp,yp,zp=unpack(B)
    d0=a*ap+inner(z,zp)+inner(y,yp)
    d1=b*bp+inner(z,zp)+inner(x,xp)
    d2=c*cp+inner(y,yp)+inner(x,xp)
    ox=oscale(F(1,2),sum8((omul(oconj(z),oconj(yp)),oscale(b,xp),oscale(cp,x),
                              omul(oconj(zp),oconj(y)),oscale(bp,x),oscale(c,xp))))
    oy=oscale(F(1,2),sum8((oscale(ap,y),omul(oconj(x),oconj(zp)),oscale(c,yp),
                              oscale(a,yp),omul(oconj(xp),oconj(z)),oscale(cp,y))))
    oz=oscale(F(1,2),sum8((oscale(a,zp),oscale(bp,z),omul(oconj(y),oconj(xp)),
                              oscale(ap,z),oscale(b,zp),omul(oconj(yp),oconj(x)))))
    return pack(d0,d1,d2,ox,oy,oz)

def echelon(rows):
    piv={}
    for rr in rows:
        r={k:F(v) for k,v in rr.items() if v}
        while r:
            c=min(r)
            if c not in piv:
                z=r[c]; piv[c]={j:v/z for j,v in r.items()}; break
            z=r[c]
            for j,v in piv[c].items():
                nv=r.get(j,F(0))-z*v
                if nv:r[j]=nv
                elif j in r:del r[j]
    return piv

def rank(rows): return len(echelon(rows))
def nullspace(rows,n):
    piv=echelon(rows); free=[j for j in range(n) if j not in piv]; out=[]
    for f in free:
        x={f:F(1)}
        for c in reversed(sorted(piv)):
            s=sum(v*x.get(j,F(0)) for j,v in piv[c].items() if j!=c)
            if s:x[c]=-s
        out.append(x)
    return out

# Octonion triality system.
OB=[]
for i in range(8):
    v=[F(0)]*8;v[i]=F(1);OB.append(tuple(v))
pairs=[(i,j) for i in range(8) for j in range(i+1,8)]
def skew_apply(pair,v):
    i,j=pair;out=[F(0)]*8;out[i]=v[j];out[j]=-v[i];return tuple(out)
trial_rows=[]
for xi in range(8):
  for yj in range(8):
    xy=omul(OB[xi],OB[yj])
    for k in range(8):
      r={}
      for q,pair in enumerate(pairs):
        v=skew_apply(pair,xy)[k]
        if v:r[q]=r.get(q,F(0))+v
        v=omul(skew_apply(pair,OB[xi]),OB[yj])[k]
        if v:r[28+q]=r.get(28+q,F(0))-v
        v=omul(OB[xi],skew_apply(pair,OB[yj]))[k]
        if v:r[56+q]=r.get(56+q,F(0))-v
      r={i:v for i,v in r.items() if v}
      if r:trial_rows.append(r)
assert rank(trial_rows)==56
TB=nullspace(trial_rows,84)
assert len(TB)==28
# Every projection A/B/C has full rank 28.
for block in range(3):
    projected=[{q:c.get(28*block+q,F(0)) for q in range(28) if c.get(28*block+q,F(0))} for c in TB]
    assert rank(projected)==28

def skew_matrix(cfs,off):
    M=[[F(0)]*8 for _ in range(8)]
    for q,(i,j) in enumerate(pairs):
        c=cfs.get(off+q,F(0)); M[i][j]+=c;M[j][i]-=c
    return M
def conj_twist(M):
    s=[1]+[-1]*7
    return [[F(s[i])*M[i][j]*F(s[j]) for j in range(8)] for i in range(8)]
def blockD(ms):
    D=[[F(0)]*27 for _ in range(27)]
    for base,M in zip((3,11,19),ms):
        for i in range(8):
            for j in range(8):D[base+i][base+j]=M[i][j]
    return D

def flat(M): return {i*27+j:v for i,row in enumerate(M) for j,v in enumerate(row) if v}

# Albert basis / product structure constants.
AB=[]
for i in range(27):
    v=[F(0)]*27;v[i]=F(1);AB.append(tuple(v))
P={}
for i in range(27):
    for j in range(i,27):
        v=jprod(AB[i],AB[j]);P[i,j]={k:c for k,c in enumerate(v) if c}
def cprod(i,j,k): return P[min(i,j),max(i,j)].get(k,F(0))

def is_derivation(D):
    for i in range(27):
      for j in range(i,27):
        lhs=[F(0)]*27;rhs=[F(0)]*27
        for ell,c in P[i,j].items():
            for k in range(27):lhs[k]+=D[k][ell]*c
        for a in range(27):
            if D[a][i]:
                for k,c in P[min(a,j),max(a,j)].items():rhs[k]+=D[a][i]*c
        for b in range(27):
            if D[b][j]:
                for k,c in P[min(i,b),max(i,b)].items():rhs[k]+=D[b][j]*c
        if lhs!=rhs:return False
    return True

triality_albert=[]
for t in TB:
    A=skew_matrix(t,0);B=skew_matrix(t,28);C=skew_matrix(t,56)
    D=blockD((conj_twist(A),B,C))
    assert is_derivation(D)
    triality_albert.append(D)
assert rank([flat(D) for D in triality_albert])==28

# Left multiplication and inner commutators.
def left(i):
    M=[[F(0)]*27 for _ in range(27)]
    for j in range(27):
        for k,c in P[min(i,j),max(i,j)].items():M[k][j]=c
    return M
L=[left(i) for i in range(27)]
def mm(A,B):
    C=[[F(0)]*27 for _ in range(27)]
    for i in range(27):
      for k in range(27):
        if A[i][k]:
          for j in range(27):
            if B[k][j]:C[i][j]+=A[i][k]*B[k][j]
    return C
def comm(A,B):
    AB=mm(A,B);BA=mm(B,A)
    return [[AB[i][j]-BA[i][j] for j in range(27)] for i in range(27)]

# Three 8-dimensional Peirce families:
# x block (off12) paired with diagonal b,
# y block (off20) paired with diagonal c,
# z block (off01) paired with diagonal a.
peirce=[]
for diag,inds in ((1,range(3,11)),(2,range(11,19)),(0,range(19,27))):
    fam=[comm(L[diag],L[i]) for i in inds]
    assert rank([flat(D) for D in fam])==8
    peirce.extend(fam)
assert rank([flat(D) for D in peirce])==24
assert rank([flat(D) for D in triality_albert+peirce])==52

print('tri(O) equation rank:',rank(trial_rows),'nullity',len(TB))
print('A/B/C projection ranks: 28,28,28')
print('triality-induced Albert derivations: 28')
print('three Peirce inner families: 8+8+8 = 24')
print('combined derivation rank: 52')
print('PASS: Der(J) = tri(O) + O + O + O at exact-rational runtime level')
