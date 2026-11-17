#!/usr/bin/env python3
from fractions import Fraction as F
from itertools import combinations

# Pure-Python exact-rational audit of the derivation algebra of the explicit
# H_3(O_Q) product used by RationalAlbertJordanProductExact.agda.
#
# It verifies:
#   27^2 = 729 unknown matrix entries for a linear endomorphism D;
#   the Leibniz/Jordan derivation equations have exact rank 677;
#   therefore the solution space has dimension 52;
#   the 351 commutators [L_ei,L_ej] span exact rank 52.
#
# Hence, at the level of this exact coordinate computation, all derivations are
# already spanned by inner Jordan derivations.

Z4=(F(0),)*4
Z8=(F(0),)*8

def qmul(a,b):
    a0,a1,a2,a3=a; b0,b1,b2,b3=b
    return (
        a0*b0-a1*b1-a2*b2-a3*b3,
        a0*b1+a1*b0+a2*b3-a3*b2,
        a0*b2-a1*b3+a2*b0+a3*b1,
        a0*b3+a1*b2-a2*b1+a3*b0,
    )

def qconj(a): return (a[0],-a[1],-a[2],-a[3])

def omul(x,y):
    a,b=x[:4],x[4:]; c,d=y[:4],y[4:]
    ac=qmul(a,c); cdb=qmul(qconj(d),b)
    da=qmul(d,a); bc=qmul(b,qconj(c))
    return tuple(ac[i]-cdb[i] for i in range(4))+tuple(da[i]+bc[i] for i in range(4))

def oconj(x): return (x[0],)+tuple(-u for u in x[1:])
def oscale(c,x): return tuple(c*u for u in x)
def inner(x,y): return omul(x,oconj(y))[0]

def unpack(v):
    return v[0],v[1],v[2],tuple(v[3:11]),tuple(v[11:19]),tuple(v[19:27])

def pack(a,b,c,x,y,z): return (a,b,c)+tuple(x)+tuple(y)+tuple(z)

def jprod(A,B):
    a,b,c,x,y,z=unpack(A); ap,bp,cp,xp,yp,zp=unpack(B)
    d0=a*ap+inner(z,zp)+inner(y,yp)
    d1=b*bp+inner(z,zp)+inner(x,xp)
    d2=c*cp+inner(y,yp)+inner(x,xp)
    ox=oscale(F(1,2),tuple(sum(t[k] for t in (
        omul(oconj(z),oconj(yp)), oscale(b,xp), oscale(cp,x),
        omul(oconj(zp),oconj(y)), oscale(bp,x), oscale(c,xp))) for k in range(8)))
    oy=oscale(F(1,2),tuple(sum(t[k] for t in (
        oscale(ap,y), omul(oconj(x),oconj(zp)), oscale(c,yp),
        oscale(a,yp), omul(oconj(xp),oconj(z)), oscale(cp,y))) for k in range(8)))
    oz=oscale(F(1,2),tuple(sum(t[k] for t in (
        oscale(a,zp), oscale(bp,z), omul(oconj(y),oconj(xp)),
        oscale(ap,z), oscale(b,zp), omul(oconj(yp),oconj(x))) for k in range(8)))
    return pack(d0,d1,d2,ox,oy,oz)

B=[]
for i in range(27):
    v=[F(0)]*27; v[i]=F(1); B.append(tuple(v))

# Sparse structure constants c_ij^k, stored only for i<=j.
P={}
for i in range(27):
    for j in range(i,27):
        v=jprod(B[i],B[j])
        P[i,j]={k:c for k,c in enumerate(v) if c}

def coeff(i,j,k):
    if i<=j: return P[i,j].get(k,F(0))
    return P[j,i].get(k,F(0))

def sparse_rank(rows):
    piv={}
    for rr in rows:
        r={k:F(v) for k,v in rr.items() if v}
        while r:
            c=min(r)
            if c not in piv:
                z=r[c]
                r={j:v/z for j,v in r.items()}
                piv[c]=r
                break
            z=r[c]; pr=piv[c]
            for j,v in pr.items():
                nv=r.get(j,F(0))-z*v
                if nv: r[j]=nv
                elif j in r: del r[j]
    return len(piv)

# Derivation equations in unknowns d[out,in], flattened as out*27+in.
derivation_rows=[]
for i in range(27):
    for j in range(i,27):
        pij=P[i,j]
        for k in range(27):
            r={}
            for ell,c in pij.items():
                q=k*27+ell; r[q]=r.get(q,F(0))+c
            for a in range(27):
                c=coeff(a,j,k)
                if c:
                    q=a*27+i; r[q]=r.get(q,F(0))-c
            for b in range(27):
                c=coeff(i,b,k)
                if c:
                    q=b*27+j; r[q]=r.get(q,F(0))-c
            r={q:c for q,c in r.items() if c}
            if r: derivation_rows.append(r)

rank_der=sparse_rank(derivation_rows)
assert rank_der==677
assert 729-rank_der==52

# Left multiplication matrices as sparse maps (row,col)->coefficient.
def left_matrix(i):
    M={}
    for j in range(27):
        for k,c in P[min(i,j),max(i,j)].items(): M[k,j]=c
    return M

def matmul(A,B):
    by_mid={}
    for (r,m),v in A.items(): by_mid.setdefault(m,[]).append((r,v))
    out={}
    for (m,c),w in B.items():
        for r,v in by_mid.get(m,[]):
            q=(r,c); out[q]=out.get(q,F(0))+v*w
    return {q:v for q,v in out.items() if v}

def comm(A,B):
    AB=matmul(A,B); BA=matmul(B,A); out=dict(AB)
    for q,v in BA.items(): out[q]=out.get(q,F(0))-v
    return {q:v for q,v in out.items() if v}

L=[left_matrix(i) for i in range(27)]
inner_rows=[]
for i,j in combinations(range(27),2):
    C=comm(L[i],L[j])
    inner_rows.append({r*27+c:v for (r,c),v in C.items()})
rank_inner=sparse_rank(inner_rows)
assert len(inner_rows)==351
assert rank_inner==52

print('derivation equations:',len(derivation_rows))
print('derivation matrix rank:',rank_der)
print('derivation nullity:',729-rank_der)
print('inner commutators:',len(inner_rows))
print('inner-derivation span rank:',rank_inner)
print('PASS: exact rational Der(J) dimension = 52 and inner span = 52')
