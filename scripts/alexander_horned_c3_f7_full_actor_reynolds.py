#!/usr/bin/env python3
"""Full finite spin/projective actor F7 Maschke and Reynolds compatibility.

Source: actual 2I=SL2(F5) -> A5 map from five conjugate Q8 subgroups.
Both full semidirect actor group orders are coprime to 7. The map of
360 to 180 site functions intertwines their normalized invariant
averaging projectors. Finite group algebra, not a physical Dirac mode.
"""
from itertools import product,combinations
from collections import Counter
p=5; z=(1,0,0,1); neg=(4,0,0,4)
def mul(x,y):
 a,b,c,d=x;e,f,g,h=y
 return ((a*e+b*g)%p,(a*f+b*h)%p,(c*e+d*g)%p,(c*f+d*h)%p)
def inv(x):a,b,c,d=x;return (d,(-b)%p,(-c)%p,a)
def power(x,n):
 v=z
 for _ in range(n):v=mul(v,x)
 return v
def conj(x,y):return mul(mul(x,y),inv(x))
def comm(x,y):return mul(mul(mul(x,y),inv(x)),inv(y))
def subgroup(gs):
 moves=tuple(gs)+tuple(inv(g) for g in gs)
 seen={z};front=[z]
 while front:
  a=front.pop()
  for g in moves:
   b=mul(a,g)
   if b not in seen:seen.add(b);front.append(b)
 return frozenset(seen)
S=tuple(x for x in product(range(5),repeat=4)
        if (x[0]*x[3]-x[1]*x[2])%5==1)
assert len(S)==120
quad=[x for x in S if power(x,2)==neg]
Q=sorted({subgroup((a,b)) for a,b in combinations(quad,2)
          if comm(a,b)==neg},key=lambda h:sorted(h))
assert len(Q)==5 and all(len(t)==8 for t in Q)
def quotient(x):return tuple(Q.index(frozenset(conj(x,t) for t in g)) for g in Q)
A5=tuple(sorted({quotient(x) for x in S}))
assert len(A5)==60
fibres=Counter(quotient(x) for x in S)
assert all(v==2 for v in fibres.values())
assert 3*60**3==648000 and 3*120**3==5184000
assert 648000%7==5184000%7==3
assert 180%7==5 and 360%7==3
assert 2*pow(360,-1,7)%7==pow(180,-1,7)==3
assert 648000*pow(648000,-1,7)%7==1
assert 5184000*pow(5184000,-1,7)%7==1
SLOTS_S=tuple((i,x) for i in range(3) for x in S)
SLOTS_A=tuple((i,x) for i in range(3) for x in A5)
assert len(SLOTS_S)==360 and len(SLOTS_A)==180
index={x:j for j,x in enumerate(A5)}
def f(i,x):return (i+3*index[x]+index[x]**2)%7
def pull(i,x):return f(i,quotient(x))
def mean_A():return sum(f(i,x) for i,x in SLOTS_A)*pow(180,-1,7)%7
def mean_S():return sum(pull(i,x) for i,x in SLOTS_S)*pow(360,-1,7)%7
assert mean_A()==mean_S()
for h in (S[0],S[1],S[17],S[47],S[-1]):
 for sector in range(3):
  assert sum(pull(i,mul(h,x) if i==sector else x)
             for i,x in SLOTS_S)%7==sum(pull(i,x) for i,x in SLOTS_S)%7
  assert sum(f(i,tuple(quotient(h)[quotient(x)[k]]
                  for k in range(5)) if i==sector else quotient(x))
             for i,x in SLOTS_S)%7==2*sum(f(i,x) for i,x in SLOTS_A)%7
assert sum(pull((i+1)%3,x) for i,x in SLOTS_S)%7==sum(pull(i,x) for i,x in SLOTS_S)%7
print('PASS genuine 2I/A5 finite group 120->60, two lifts per element')
print('PASS full actor orders 648000 and 5184000 both = 3 mod 7')
print('PASS Reynolds averaging across 180->360 site scalar pullback over F7')
print('PASS local left translations and external sector rotation preserve means')
print('Maschke over F7 applies to BOTH full actors; over F5 only to C3')
print('Not proven: Agda kernel field/group instance, physical spectral claims')
