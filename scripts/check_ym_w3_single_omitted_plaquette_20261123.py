#!/usr/bin/env python3
"""Original L4 two-time Wilson single-extra-plaquette census, exact arithmetic.
Only one extra interaction at a time; never a full homogeneous W3 bound.
Uses imported standard continuous SU(N) Haar character convolution for the
conditional-intermediate-cap law; checks original incidence and SU2 moments.
"""
from collections import Counter
from itertools import combinations, product
import sympy as S
L=4
sites=tuple(product(range(L), repeat=4))
def step(x,a):
    y=list(x);y[a]=(y[a]+1)%L;return tuple(y)
def face(x,a,b):
    return ((x,a,1),(step(x,a),b,1),(step(x,b),a,-1),(x,b,-1))
faces={(x,a,b):face(x,a,b) for x in sites for a,b in combinations(range(4),2)}
assert (len(sites),len(faces))==(256,1536)
def support(p):return frozenset((x,a) for x,a,_ in faces[p])
def walls(d):
    return tuple(((t,dy,dz,0),0,a) for t in range(d) for a in (1,2)
                 for dy,dz in ([(0,0),(0,1)] if a==1 else [(0,0),(1,0)]))
def parity(ps):
    counts=Counter((x,a) for p in ps for x,a,_ in faces[p])
    return frozenset(e for e,n in counts.items() if n%2)
for d in (1,2):
    F=((0,0,0,0),1,2);G=((d,0,0,0),1,2);H=((1,0,0,0),1,2)
    T=walls(d);old=(F,G)+T
    assert not parity(old)
    union=frozenset().union(*(support(p) for p in old))
    assert len(union)==8*d+4
    omitted=set(faces)-set(T)
    internal={p for p in omitted if support(p)<=union}
    expected={F,G}|({H} if d==2 else set())
    assert internal==expected
    external=omitted-internal
    hist=Counter(len(support(p)-union) for p in external)
    if d==1:
        assert len(external)==1530 and hist==Counter({3:48,4:1482})
    else:
        assert len(external)==1525 and hist==Counter({3:76,4:1449})
    print('PASS d=%d: 4d=%d wall, %d omitted; inside=%d, external=%d, new-edge histogram=%s' %
          (d,len(T),len(omitted),len(internal),len(external),dict(hist)))

# An independent off-tube plaquette has a unique independent Haar link;
# integrating that link turns its exp(eta*t_p) into the constant z_N(eta).
# This is exactly source-invisible for ONE extra plaquette, any real eta.
# Five distinct external plaquettes together can replace one wall face:
def cube(x,axes):
    a,b,c=axes
    return frozenset(((x,a,b),(step(x,c),a,b),(x,a,c),(step(x,b),a,c),
                      (x,b,c),(step(x,a),b,c)))
cubes={cube(x,axes) for x in sites for axes in combinations(range(4),3)}
F=((0,0,0,0),1,2);G=((2,0,0,0),1,2);T=set(walls(2))
candidates=[c for c in cubes if len(c&T)==1 and F not in c and G not in c]
assert len(candidates)==24
for c in candidates:
    new={F,G}|(T-(c&T))|(c-T)
    assert len(new)==14 and not parity(new)
    edges=Counter((x,a) for p in new for x,a,_ in faces[p])
    vertices=set()
    for x,a,b in new:
        vertices.update((x,step(x,a),step(x,b),step(step(x,a),b)))
    assert len(edges)==28 and all(n==2 for n in edges.values())
    assert len(vertices)==16 and len(vertices)-len(edges)+len(new)==2
print('PASS 24 original 3D cube flips replace one wall with five spectators')

# Original continuous SU2 Haar fundamental real trace moments:
# E_Haar[t^(2n)] = Catalan(n)/4^n.  Not a finite subgroup Haar sample.
x=S.symbols('x')
z=sum(S.catalan(n)*x**(2*n)/(S.Integer(4)**n*S.factorial(2*n))
      for n in range(9))
m=S.series(S.diff(z,x)/z,x,0,9).removeO().expand()
v=S.series(S.diff(z,x,2)/z-(S.diff(z,x)/z)**2,x,0,8).removeO().expand()
assert v==S.expand(S.diff(m,x))
assert v==S.Rational(1,4)-x*x/32+5*x**4/1536-7*x**6/23040
beta,eta=S.symbols('beta eta')
a=S.series(m.subs(x,beta)**4,beta,0,7).removeO().expand()
cov=S.expand(a*a*v.subs(x,eta))
assert cov.coeff(beta,8).coeff(eta,0)==S.Rational(1,262144)
assert cov.coeff(beta,8).coeff(eta,2)==-S.Rational(1,2097152)
assert cov.coeff(beta,8).coeff(eta,4)==S.Rational(5,100663296)
assert cov.coeff(beta,10).coeff(eta,0)==-S.Rational(1,786432)
print('PASS exact continuous SU2 moments and intermediate H variance jets')
print('SOURCE FORMULA: Cov(F,G)=m_N_prime(eta)*product_8walls m_N(beta_q)')
print('OPEN multiple spectators, unrestricted homogeneous 4D Wilson, CMP119/122, W3, OS')
