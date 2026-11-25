from itertools import product
from collections import Counter
from pathlib import Path
from runpy import run_path
from sympy import Poly, symbols, cyclotomic_poly

# Original R261 arithmetic; donor #1552 uses pi'=zeta-1=-pi.
b=run_path(str(Path(__file__).with_name('check_langlands_wild_epsilon_20261125.py')))
add,mul,red,chi,phase=[b[k] for k in ('add','mul','red','chi','phase')]
Z=(0,0); O=(1,0); pi=(0,1)
def neg(x):return tuple(-a for a in x)
def sub(x,y):return add(x,neg(y))
def sq(x):return mul(x,x)
def norm(x):a,c=x;return red(add(sq(a),sq(c)))
def mm(x,y):
    a,c=x;d,e=y
    return red(sub(mul(a,d),mul(c,e))),red(add(mul(a,e),mul(c,d)))
def pp(x,n):
    r=(O,Z)
    for _ in range(n):r=mm(r,x)
    return r
ring=list(product(range(9),repeat=2));units=[(a,c) for a,c in product(ring,repeat=2) if (a[0]%3,c[0]%3)!=(0,0)]
counts=Counter(norm(x) for x in units);assert len(counts)==54 and set(counts.values())=={108}
assert Counter(chi[norm(x)] for x in units)=={0:1944,1:1944,2:1944}
# Unramified Frobenius i->-i and ramified conjugation pi->3-pi.
def tau(a):return red((a[0]+3*a[1],-a[1]))
for a,c in units:
    assert norm((a,red(neg(c))))==norm((a,c))
    assert chi[norm((tau(a),tau(c)))]==(-chi[norm((a,c))])%3
# The donor's twelve phases lie in the cubic norm kernel, not the three signed characters.
zeta=(1,-1); rho=(Z,red(zeta)); orbit=[pp(rho,j) for j in range(12)]
assert len(set(orbit))==12 and all(chi[norm(x)]==0 for x in orbit)
# Norm pullback, exact full wild Gauss sum on actual O_K2/9 (not just stationarity).
# Trace to K sends (a,c) to 2a, additive phases in mu9.
T=symbols('T');P=Poly(cyclotomic_poly(9,T),T)
for s in (1,-1):
    C=Counter((phase(add(a,a))-3*s*chi[norm((a,c))])%9 for a,c in units)
    assert Poly(sum(v*T**k for k,v in C.items()),T)%P==Poly(81,T)
print('norm units',len(units),'fibres',len(counts),'size',next(iter(counts.values())),'phase kernel',len(orbit),'Gauss 81 both orientations')

# Mixed quotient of the actual R255 Weil image: S3 x (C5 semidirect Z).
# Geometric Frobenius acts by 3^-1=2 on tame exponents; retain full degree k.
def gm(x,y):
    a,b,t,k=x; A,B,U,K=y
    return ((a+(-1)**b*A)%3,(b+B)%2,(t+pow(2,k,5)*U)%5,k+K)
def gi(x):
    a,b,t,k=x;return ((-(-1)**b*a)%3,b,(-pow(2,-k,5)*t)%5,-k)
def key(x):return x[:3]+(x[3]%4,)
G=list(product(range(3),range(2),range(5),range(4)))
H=lambda x:x[1]==0 and x[3]%4==0 # W_E4
I=lambda x:x[3]%2==0 # W_F2
J=lambda x:x[0]==0 and x[3]%2==0 # W_LF2, nonnormal
K=lambda x:H(x) and J(x)
def reps(outer,inner):
    R=[];covered=set()
    for a in G:
        if outer(a) and key(a) not in covered:
            R.append(a);covered.update(key(gm(a,h)) for h in G if inner(h))
    return R
def decomp(x,R,inner):
    for i,c in enumerate(R):
        h=gm(gi(c),x)
        if inner(h):return i,h
    raise AssertionError(x)
# scalar exact monomial (zeta3 exponent,zeta5 exponent,alpha exponent,3 exponent).
def sc(x,y):return ((x[0]+y[0])%3,(x[1]+y[1])%5,x[2]+y[2],x[3]+y[3])
def hc(h,i):
    assert H(h);return h[0],h[2],h[3]//4,h[3]*i

def action(t,c,R,inner,i):
    j,h=decomp(gm(t,c),R,inner);return j,hc(h,i)
R=reps(lambda x:True,H);A=reps(lambda x:True,I);B=reps(I,H)
assert len(R)==8 and len(A)==2 and len(B)==4
# Actual arbitrary nonzero Weil degrees, not finite quotient modulus.
gens=[(1,0,0,0),(0,1,0,0),(0,0,1,0),(0,0,0,1),(0,0,0,-1),(2,1,3,7),(1,0,2,-5)]
checks=Counter()
for t,c,i in product(gens,R,range(1,4)):
    j,s=action(t,c,R,H,i);jj,u=action(t,c,R,H,i-1)
    assert j==jj and sc(s,(0,0,0,R[j][3]))==sc(u,(0,0,0,c[3]+t[3]))
    checks['WD_covariance']+=1
for t,u,c,i in product(gens,gens,R,range(4)):
    j,s=action(u,c,R,H,i);k,v=action(t,R[j],R,H,i);kk,w=action(gm(t,u),c,R,H,i)
    assert k==kk and sc(s,v)==w;checks['group_action']+=1
# Transitivity across unramified F2 with independently shifted coset gauges.
AA=[gm(a,(0,0,0,2*(i+1))) for i,a in enumerate(A)]
BB=[gm(b,(i%3,0,i%5,4*(i-2))) for i,b in enumerate(B)]
for a,b,i in product(AA,BB,range(4)):
    j,h0=decomp(gm(a,b),R,H)
    for t in gens:
        aa,u=decomp(gm(t,a),AA,I);bb,h1=decomp(gm(u,b),BB,H)
        jj,h2=decomp(gm(AA[aa],BB[bb]),R,H)
        j3,s3=action(t,R[j],R,H,i)
        assert jj==j3 and sc(hc(h1,i),hc(h2,i))==sc(hc(h0,i),s3)
        checks['tower_gauge']+=1
    if i:
        assert sc(hc(h0,i),(0,0,0,R[j][3]))==sc(hc(h0,i-1),(0,0,0,a[3]+b[3]))
        checks['tower_N']+=1
# Restriction to the nonnormal mixed field LF2. Two J\G/H sectors, anchor g with degree0 or1.
C=reps(J,K);assert len(C)==4
for g in [(0,0,0,0),(0,0,0,1)]:
    for c,i in product(C,range(4)):
        j,h0=decomp(gm(c,g),R,H)
        for t in [x for x in gens if J(x)]+[(0,1,1,2),(0,0,3,-2)]:
            cc,h=decomp(gm(t,c),C,K);h1=gm(gm(gi(g),h),g)
            jj,h2=decomp(gm(C[cc],g),R,H);j3,s3=action(t,R[j],R,H,i)
            assert jj==j3 and sc(hc(h1,i),hc(h2,i))==sc(hc(h0,i),s3)
            checks['nonnormal_gauge']+=1
        if i:
            assert sc(hc(h0,i),(0,0,0,R[j][3]))==sc(hc(h0,i-1),(0,0,0,c[3]+g[3]))
            checks['nonnormal_N']+=1
print(dict(checks))
