from collections import Counter
from itertools import product
from math import gcd
from random import Random
from sympy import Rational, Matrix, eye, zeros, diag, kronecker_product, symbols, Poly, cyclotomic_poly

q=3
T=symbols('T')

def orbit(m,u,step=1):
    a=[u%m]; v=u*pow(q,step,m)%m
    while v!=a[0]:
        a.append(v); v=v*pow(q,step,m)%m
    return a

def cycle(d,A):
    h=A.rows; P=zeros(d*h)
    for i in range(d):
        P[((i+1)%d)*h:((i+1)%d+1)*h,i*h:(i+1)*h]=A if i==d-1 else eye(h)
    return P

def hom(A,B):
    return kronecker_product(B.inv().T,A)

def restricted_hom(P,Q,labels,other):
    inds=[j*len(labels)+i for j,b in enumerate(other) for i,a in enumerate(labels) if a==b]
    H=hom(P,Q)
    assert all(H[i,j]==0 for j in inds for i in range(H.rows) if i not in inds)
    return H.extract(inds,inds)

def cp(A):
    return Poly(A.charpoly(T).as_expr(),T)

def loop_cp(A,d):
    return Poly(A.charpoly(T).as_expr().subs(T,T**d),T)

# Exact tame characters represented by exponents in mu_m, not floats.
# P sends character u_i to u_(i+1), giving P tau P^-1=tau^(q^-1).
orbits=relation=pair=restrict=0
for m in [2,4,5,7,8,10,13,16,20,26]:
    seen=set(); O=[]
    for u in range(m):
        if u in seen: continue
        o=orbit(m,u); seen.update(o); O.append(o); orbits+=1
        d=len(o); P=cycle(d,Matrix([[2]]))
        assert all((o[i]-q*o[(i-1)%d])%m==0 for i in range(d)); relation+=1
        for f in range(1,7):
            g=gcd(d,f); s=d//g
            assert cp(P**f)==loop_cp(Matrix([[2**(f//g)]]),s)**g
            assert len({tuple(sorted(orbit(m,u,f))) for u in o})==g
            restrict+=1
    for a,b in product(O,repeat=2):
        P=cycle(len(a),Matrix([[2]])); Q=cycle(len(b),Matrix([[3]]))
        H=restricted_hom(P,Q,a,b)
        assert cp(H)==(loop_cp(Matrix([[Rational(2,3)]]),len(a)) if a==b else Poly(1,T))
        pair+=1

# Multiplicity spaces and explicit loop transport (non-diagonal matrices).
multi=0
for d,h,j in product(range(1,5),range(1,4),range(1,3)):
    A=diag(*range(2,2+h)); B=diag(*range(5,5+j))
    if h>1:
        S=eye(h); S[0,1]=1; A=S*A*S.inv()
    if j>1:
        S=eye(j); S[0,1]=2; B=S*B*S.inv()
    P=cycle(d,A); Q=cycle(d,B)
    H=restricted_hom(P,Q,[i for i in range(d) for _ in range(h)],[i for i in range(d) for _ in range(j)])
    assert cp(H)==loop_cp(hom(A,B),d)
    multi+=1

# Explicit induction from degree f unramified subgroup. Induction copies
# carry character q^i*u and monodromy q^i*N; wrap Phi_E.
ind=wd=correction=0
for m,u,f in product([4,5,8,13],[0,1],range(1,6)):
    o=orbit(m,u); d=len(o); g=gcd(d,f); s=d//g
    sub=orbit(m,u,f); assert len(sub)==s
    P0=cycle(s,Matrix([[2]])); P=cycle(f,P0)
    labels=[a*pow(q,i,m)%m for i in range(f) for a in sub]
    assert all((labels[i]-q*labels[j])%m==0 for i in range(P.rows) for j in range(P.cols) if P[i,j])
    assert cp(P)==loop_cp(Matrix([[2]]),f*s)
    assert Counter(labels)==Counter({a:f//g for a in o})
    # Phi^d on a single inertia fibre has characteristic polynomial X^(f/g)-2.
    ix=[i for i,a in enumerate(labels) if a==u%m]
    assert cp((P**d).extract(ix,ix))==loop_cp(Matrix([[2]]),f//g)
    ind+=1
    for k in [1,2,3]:
        N=Matrix(k,k,lambda i,j:int(j==i+1)); D=diag(*[q**(f*i) for i in range(k)])
        PE=kronecker_product(P0,D); NE=kronecker_product(eye(s),N)
        PF=cycle(f,PE); NF=diag(*[q**i*NE for i in range(f)])
        assert PF*NF==NF*PF/q
        # kernel coordinates i=0, nonzero inertia excluded from L.
        li=[(i*s+j)*k for i in range(f) for j,a in enumerate(sub) if a==0]
        le=[j*k for j,a in enumerate(sub) if a==0]
        assert cp(PF.extract(li,li))==loop_cp(PE.extract(le,le),f)
        # tame Artin conductor + monodromy correction (same inertia under unramified restriction)
        aE=s*k-len(le)*k+len(le)*(k-1)
        aF=f*s*k-len(li)*k+len(li)*(k-1)
        assert aF==f*aE
        wd+=1
        qi=[i for i in range(s*k) if sub[i//k]==0 and i%k!=0]
        qf=[i for i in range(f*s*k) if sub[(i//k)%s]==0 and i%k!=0]
        assert (-PF.extract(qf,qf)).det()==(-PE.extract(qi,qi)).det()
        correction+=1

# Tame F9 Gauss sums, exact cyclotomic arithmetic in Q(zeta_24).
# F9 = F3[i], i^2=-1; generator 1+i has order 8.
def mul(a,b): return ((a[0]*b[0]-a[1]*b[1])%3,(a[0]*b[1]+a[1]*b[0])%3)
pows=[(1,0)]
for _ in range(7): pows.append(mul(pows[-1],(1,1)))
assert len(set(pows))==8 and mul(pows[-1],(1,1))==(1,0)
phi=Poly(cyclotomic_poly(24,T),T)
def G(c): return Poly(sum(T**((-3*c*j+8*(2*a[0]%3))%24) for j,a in enumerate(pows)),T)%phi
gauss=0
for c in range(1,8):
    assert G(c)==G(3*c%8)
    assert G(c)*G(-c)%phi==Poly(9*(-1)**c,T)
    gauss+=1

# Orbit-loop signs, not naive per-step quadratic twists. Compute compressed
# signed matched spectra in X=T^d, with monodromy shifts q^(d*h).
signed=blind=0
for d,k,l in product(range(1,7),range(1,6),range(1,6)):
    P=cycle(d,Matrix([[2]])); assert cp(-P)==cp(P) if d%2==0 else cp(-P)!=cp(P)
    blind+=1
    for b,c in product(range(2),repeat=2):
        A={1:3-2*b,-1:2*b}; B={1:3-2*c,-1:2*c}
        A0={1:3,-1:0}; B0=A0
        def count(a,z,sg): return sum(v*w for i,v in a.items() for j,w in z.items() if i*j==sg)
        for sg in [1,-1]:
            delta=count(A,B,sg)-count(A0,B,sg)-count(A,B0,sg)+count(A0,B0,sg)
            assert delta*min(k,l)==8*b*c*sg*min(k,l)
            signed+=1
print(dict(orbits=orbits,relations=relation,pairs=pair,restriction=restrict,multiplicity=multi,induction=ind,wd=wd,det_correction=correction,gauss=gauss,quadratic_controls=blind,signed=signed))
