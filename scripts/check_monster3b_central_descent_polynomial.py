#!/usr/bin/env python3
"""Universal central group-algebra identities, not a native Monster fixture."""
import sympy as sp

z,t=sp.symbols('z t')
G=sp.groebner([z**3-1,t*t+t+1],z,t,domain=sp.QQ)
checks=0
def red(p):return G.reduce(sp.expand(p))[1]
def eq(a,b):
    global checks
    if red(a-b)!=0:raise ValueError((a,b,red(a-b)))
    checks+=1
P=[red(sum(t**((-s*j)%3)*z**j for j in range(3))/3) for s in range(3)]
eq(sum(P),1)
for s in range(3):
    eq(z*P[s],t**s*P[s])
    eq(P[s].subs(z,z*z),P[(-s)%3])
    for r in range(3):eq(P[s]*P[r],P[s] if r==s else 0)
    for a in range(3):
        eq(t**((s*a)%3)*t**((-s*a)%3),1)
        eq(z**a*P[s],t**((s*a)%3)*P[s])
# Scalar actions of the two original central factors need not be trivial.
if red(t-1)==0 or red(t*t-1)==0:raise ValueError('collapsed nontrivial phase')
checks+=2
print({'status':'UNIVERSAL_CENTRAL_GROUP_ALGEBRA_IDENTITIES','checks':checks,'projectors':[str(p) for p in P]})
