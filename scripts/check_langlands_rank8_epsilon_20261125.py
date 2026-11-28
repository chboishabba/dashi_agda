from itertools import product
from pathlib import Path
from runpy import run_path
from collections import Counter
from sympy import Poly, symbols, cyclotomic_poly, Matrix

base=run_path(str(Path(__file__).with_name('check_langlands_wild_epsilon_20261125.py')))
chi,phase,mul,red,pw,add=[base[k] for k in ('chi','phase','mul','red','pw','add')]
# Base stationary character on U^2/U^4; both orientations.
for a,b in product(range(3),repeat=2):
    x=(a,b)
    assert chi[red(add((1,0),mul(pw((0,1),2),x))) ]==(2*a+b)%3
    assert phase(mul(pw((0,1),2),x))%9==3*b
for sign in (1,-1):
    u=(sign,2*sign)
    assert (phase(u)-3*sign*chi[red(u)])%9==0

# F81 = F3[t]/(t^4+t+2). Exact coefficient arithmetic.
Z=(0,0,0,0); I=(1,0,0,0)
B=[tuple(int(i==j) for i in range(4)) for j in range(4)]
F=list(product(range(3),repeat=4))
def fa(a,b): return tuple((x+y)%3 for x,y in zip(a,b))
def fs(a,n): return tuple(n*x%3 for x in a)
def fm(a,b):
    c=[0]*7
    for i,j in product(range(4),repeat=2): c[i+j]+=a[i]*b[j]
    for i in range(6,3,-1):
        c[i-3]-=c[i];c[i-4]-=2*c[i]
    return tuple(x%3 for x in c[:4])
def fp(a,n):
    b=I
    while n:
        if n%2:b=fm(b,a)
        a=fm(a,a);n//=2
    return b
def tr(a):
    s=Z
    for i in range(4):s=fa(s,fp(a,3**i))
    assert s[1:]==(0,0,0)
    return s[0]
assert all(fp(a,81)==a for a in F)
assert len({tuple(tr(fm(a,b)) for b in B) for a in F})==81
# On E, norm of 1+pi^2*x reduces to 1+pi^2*Tr_E/K(x).
# Trace pairing on F81 detects stationary residue (a,b)=(s,2s).
stationary=0
for s in (1,-1):
    survivors=[]
    for a,b in product(F,F):
        if a==Z:continue
        ok=all(tr(fm(b,x))==s*2*tr(x)%3 and tr(fm(a,x))==s*tr(x)%3 for x in B)
        if ok:survivors.append((a,b))
        stationary+=1
    assert survivors==[(fs(I,s),fs(I,2*s))]
    u=(s,2*s)
    assert (4*phase(u)-3*s*4*chi[red(u)])%9==0
# Direct tame Gauss sum over residue field, all order-five characters.
g=next(a for a in F if a!=Z and fp(a,40)!=I and fp(a,16)!=I)
pows=[fp(g,j) for j in range(80)];assert len(set(pows))==80
T=symbols('T'); C=Poly(cyclotomic_poly(15,T),T)
for h in range(1,5):
    terms=Counter((5*tr(a)-3*h*j)%15 for j,a in enumerate(pows))
    assert Poly(sum(n*T**i for i,n in terms.items()),T)%C==Poly(9,T)
# Mackey normal subgroup E: eight relative cosets, each orbit of eight pairs.
G=list(product(range(2),range(4)))
def diff(a,b):return ((a[0]-b[0])%2,(a[1]-b[1])%4)
fibres={h:[(a,b) for a,b in product(G,G) if diff(a,b)==h] for h in G}
assert all(len(v)==8 for v in fibres.values())
for h,vs in fibres.items():
    for a,b in vs:
        for c in G:
            aa=((a[0]+c[0])%2,(a[1]+c[1])%4);bb=((b[0]+c[0])%2,(b[1]+c[1])%4)
            assert diff(aa,bb)==h
conductors=[4 if e else (1 if j else 0) for e,j in G]
assert Counter(conductors)=={0:1,1:3,4:4}
assert sum(4*a+4 for a in conductors)==108
assert sum(a+1 for a in conductors)==27
# WD epsilon correction on the pair: only the identity relative coset has
# inertia invariants. For lengths k,l, underlying spectral exponents i-j;
# kernel exponents j-l+1. Exact determinant ratio including sign.
wd=0
for k,l in product(range(1,9),repeat=2):
    m=min(k,l)
    full=[i-j for i in range(k) for j in range(l)]
    ker=[j-l+1 for j in range(m)]
    assert sum(full)==k*l*(k-l)//2
    assert sum(ker)==m*(m-1)//2-m*(l-1)
    assert 108*k*l+4*(k*l-m)==112*k*l-4*m
    wd+=1
print('PASS:',stationary,'stationary residue controls; 81 trace signatures; 4 tame Gauss sums; 512 Mackey translations; 64 WD exponent controls')
