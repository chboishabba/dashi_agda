#!/usr/bin/env python3
"""Exact 2I=SL2(F5) -> SL2(F49) -> GL4(F7): minimal nontrivial F7 degree.

Sources: Klein/Hamilton binary icosahedral 120-unit quaternions and
scalar restriction. Every finite group product and same-object map is checked.
No Agda-kernel, wild pi1 or physical Dirac/Monster recognition is inferred.
"""
from itertools import product,permutations,combinations

P=7
def E(a=0,b=0):return (a%P,b%P)
Z=E();ONE=E(1);T=E(0,1);HALF=E(4)
def ea(x,y):return E(x[0]+y[0],x[1]+y[1])
def en(x):return E(-x[0],-x[1])
def es(x,y):return ea(x,en(y))
def em(x,y):return E(x[0]*y[0]+5*x[1]*y[1],x[0]*y[1]+x[1]*y[0])
def ep(x,n):
    out=ONE
    for _ in range(n):out=em(out,x)
    return out
assert ep(T,2)==E(5)
phi=em(HALF,ea(ONE,T));phi_inverse=es(phi,ONE)
assert em(phi,phi_inverse)==ONE
QI=(ONE,Z,Z,Z);QN=(en(ONE),Z,Z,Z)
def qa(a,b):return tuple(ea(x,y) for x,y in zip(a,b))
def qs(a,k):return tuple(em(k,x) for x in a)
def qm(a,b):
    w,x,y,z=a;W,X,Y,V=b
    return (es(es(es(em(w,W),em(x,X)),em(y,Y)),em(z,V)),
            ea(ea(es(em(w,X),em(z,Y)),em(x,W)),em(y,V)),
            ea(ea(es(em(w,Y),em(x,V)),em(y,W)),em(z,X)),
            ea(ea(es(em(w,V),em(y,X)),em(x,Y)),em(z,W)))
def qp(x,n):
    out=QI
    for _ in range(n):out=qm(out,x)
    return out
def norm(q):
    out=Z
    for a in q:out=ea(out,em(a,a))
    return out
def parity_even(t):
    return sum(t[i]>t[j] for i in range(len(t)) for j in range(i+1,len(t)))%2==0

icosians=set()
for i in range(4):
    for sign in (-1,1):
        v=[Z]*4;v[i]=E(sign);icosians.add(tuple(v))
for signs in product((-1,1),repeat=4):
    icosians.add(tuple(E(4*s) for s in signs))
for perm in permutations(range(4)):
    if not parity_even(perm):continue
    for signs in product((-1,1),repeat=3):
        v=(Z,E(signs[0]),em(E(signs[1]),phi),em(E(signs[2]),phi_inverse))
        icosians.add(tuple(em(HALF,v[perm[i]]) for i in range(4)))
assert len(icosians)==120 and all(norm(q)==ONE for q in icosians)
assert all(qm(a,b) in icosians for a in icosians for b in icosians)
assert {q for q in icosians if qp(q,2)==QI}=={QI,QN}

# Split the Hamilton quaternion algebra using explicit F7 matrices.
def mm(a,b):
    x,y,z,w=a;X,Y,V,W=b
    return ((x*X+y*V)%P,(x*Y+y*W)%P,(z*X+w*V)%P,(z*Y+w*W)%P)
I2=(1,0,0,1);NEG2=(6,0,0,6)
def negate(a):return tuple(-x%P for x in a)
mi=next(a for a in product(range(P),repeat=4) if mm(a,a)==NEG2)
mj=next(b for b in product(range(P),repeat=4)
        if mm(b,b)==NEG2 and mm(mi,b)==negate(mm(b,mi)))
mk=mm(mi,mj)
basis=(I2,mi,mj,mk)
def embed(q):
    return tuple(
        ea(ea(em(q[0],E(basis[0][i])),em(q[1],E(basis[1][i]))),
           ea(em(q[2],E(basis[2][i])),em(q[3],E(basis[3][i]))))
        for i in range(4))
def mul49(a,b):
    return (ea(em(a[0],b[0]),em(a[1],b[2])),
            ea(em(a[0],b[1]),em(a[1],b[3])),
            ea(em(a[2],b[0]),em(a[3],b[2])),
            ea(em(a[2],b[1]),em(a[3],b[3])))
assert len({embed(q) for q in icosians})==120
# Hamilton quaternion norm=1 implies determinant 1; check literal
# determinant rather than relying only on that classical identity.
assert all(es(em(embed(q)[0],embed(q)[3]),
              em(embed(q)[1],embed(q)[2]))==ONE for q in icosians)

for a in icosians:
    for b in icosians:assert embed(qm(a,b))==mul49(embed(a),embed(b))
def fldmatrix(z):return ((z[0],5*z[1]%P),(z[1],z[0]))
def restrict(q):
    a,b,c,d=q
    A,B,C,D=map(fldmatrix,(a,b,c,d))
    return tuple(tuple((A if i<2 and j<2 else B if i<2 else
                        C if j<2 else D)[i%2][j%2]
                       for j in range(4)) for i in range(4))
def mul4(a,b):
    return tuple(tuple(sum(a[i][k]*b[k][j] for k in range(4))%P
                       for j in range(4)) for i in range(4))
assert len({restrict(embed(q)) for q in icosians})==120
for a in icosians:
    for b in icosians:
        assert restrict(embed(qm(a,b)))==mul4(restrict(embed(a)),restrict(embed(b)))
assert restrict(embed(QN))==tuple(tuple(6 if i==j else 0 for j in range(4)) for i in range(4))

# Construct a literal same-group isomorphism SL2(F5) -> the 120 icosians.
def s_mul(a,b):
    x,y,z,w=a;X,Y,V,W=b
    return ((x*X+y*V)%5,(x*Y+y*W)%5,(z*X+w*V)%5,(z*Y+w*W)%5)
def s_pow(a,n):
    out=(1,0,0,1)
    for _ in range(n):out=s_mul(out,a)
    return out
SL=tuple((a,b,c,d) for a,b,c,d in product(range(5),repeat=4)
         if (a*d-b*c)%5==1)
S1=(1,0,0,1);SN=(4,0,0,4)
assert len(SL)==120
def generated(gs,identity,prod):
    seen={identity};todo=[identity]
    while todo:
        x=todo.pop()
        for g in gs:
            v=prod(x,g)
            if v not in seen:seen.add(v);todo.append(v)
    return seen
def find_pair(group,ident,minus,product,power):
    a4=[a for a in group if power(a,2)==minus]
    b6=[b for b in group if power(b,3)==minus and power(b,6)==ident]
    for a in a4:
        for b in b6:
            if power(product(a,b),5)==minus and len(generated((a,b),ident,product))==120:
                return a,b
    raise AssertionError("missing (2,3,5) generators")
sa,sb=find_pair(SL,S1,SN,s_mul,s_pow)
ua,ub=find_pair(icosians,QI,QN,qm,qp)
equivalence={S1:QI};todo=[S1]
while todo:
    x=todo.pop()
    for sg,ug in ((sa,ua),(sb,ub)):
        xx=s_mul(x,sg);yy=qm(equivalence[x],ug)
        if xx in equivalence:assert equivalence[xx]==yy
        else:equivalence[xx]=yy;todo.append(xx)
assert len(equivalence)==120 and set(equivalence.values())==icosians
assert equivalence[SN]==QN
for a in SL:
    for b in SL:assert equivalence[s_mul(a,b)]==qm(equivalence[a],equivalence[b])

# Genuine GALOIS/field descent, different from a mere dimension count:
# F49/F7 is quadratic and Frobenius takes sqrt(5) to -sqrt(5).
# The two 2D spin characters of 2I are Galois conjugates; an order-5
# element has trace outside F7. Restriction of scalars produces the
# four-dimensional F7 module, with character trace Tr_F49/F7.
def frobenius(x):return E(x[0],-x[1])
for a in product(range(7),repeat=2):
    assert ep(a,7)==frobenius(a)
galois_trace_witness=None
for g in icosians:
    mat=embed(g)
    trace49=ea(mat[0],mat[3])
    trace4=sum(restrict(mat)[i][i] for i in range(4))%P
    assert trace4==(trace49[0]+frobenius(trace49)[0])%P
    if g!=QI and qp(g,5)==QI and trace49!=frobenius(trace49):
        galois_trace_witness=trace49
assert galois_trace_witness is not None
print("PASS Frobenius-paired 2D spin characters over F49; nontrivial order-5 trace",
      galois_trace_witness)

# Minimality: a nontrivial 2I representation in characteristic 7
# has degree >=4, since order-5 elements generate ALL 120 source elements
# yet no GL_d(F7), d <=3, contains 5-torsion.
five=[g for g in SL if g!=S1 and s_pow(g,5)==S1]
assert len(five)>0 and len(generated(five,S1,s_mul))==120
for d in (1,2,3):
    order=1
    for j in range(d):order*=P**d-P**j
    assert order%5!=0
print("PASS: 120 unit icosians over F49 and all 14400 group products")
print("PASS: faithful 2I -> SL2(F49) -> GL4(F7), all 14400 matrix products")
print("PASS: explicit SL2(F5) to quaternion icosian group isomorphism, all 14400 products")
print("PASS: center -1 acts as -I4, invisible in quotient A5")
print("PASS: degree 4 is MINIMAL for any nontrivial 2I module over F7")
print("NOT CLAIMED: 2D F7 2I spinor, geometric horn pi1, physical Dirac/McKay/Monster recognition")
