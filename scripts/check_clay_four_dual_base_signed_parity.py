import sympy as s
from itertools import permutations
from math import gcd
counts = {}
def check(group, condition):
    if not condition: raise RuntimeError(group)
    counts[group] = counts.get(group,0)+1
# Formal aligned-prefix identity: independent symbols S_N,S_2N,S_3N,S_6N, multipliers a,b.
x,y,z,w,a,b=s.symbols('x y z w a b')
check('RH', s.expand((w-a*z)-b*(y-a*x)-(w-b*y)+a*(z-b*x))==0)
for m in range(2,10):
    for n in range(1,11):
        vals=[s.Rational(1,k)**2 for k in range(1,m*n+1)]
        e=sum((1-m*int(k%m==0))*v for k,v in enumerate(vals,1))
        check('RH',e==sum(vals)-s.Rational(1,m)*sum(vals[:n]))
# CRT / numerator obstruction and product formula threshold control.
for n in range(1,13):
    mod=55**n
    for r in [s.Rational(-7,3),s.Rational(0),s.Rational(4,9),s.Rational(11,2)]:
        B=mod**2+1; A=mod*int(s.floor(r*B/mod))
        check('BSD',A%5**n==A%11**n==0 and gcd(B,55)==1 and abs(s.Rational(A,B)-r)<s.Rational(mod,B))
# Negative strain exact contraction; actual pointwise symmetric/antisymmetric identities.
for k in range(-4,5):
    G=s.Matrix([[k,2,-1],[-3,1,k],[4,2,-k-1]])
    S=(G+G.T)/2
    for i in range(1,6):
        U=s.Matrix([[i,k,1],[2,-i,3],[k,1,2]])
        A=U.T*U
        check('NS',s.trace(G*A)==s.trace(S*A) and s.trace(S)==0 and s.trace(A)==sum(t*t for t in U))
# Group parity sign and signed orbit coefficients, on S6 cosets for sample stabilizers.
P=list(permutations(range(6))); I=tuple(range(6))
def mul(p,q):return tuple(p[q[i]] for i in range(6))
def sign(p):return (-1)**sum(p[i]>p[j] for i in range(6) for j in range(i+1,6))
def group(gs):
    H={I}; todo=[I]
    while todo:
        p=todo.pop()
        for g in gs:
            q=mul(p,g)
            if q not in H: H.add(q);todo.append(q)
    return H
for gens in [[],[(1,0,2,3,4,5)],[(1,2,0,3,4,5)],[(1,0,3,2,4,5)],[(1,2,3,4,5,0)],[(1,2,0,3,4,5),(0,1,2,4,5,3)],[(1,2,0,3,4,5),(1,0,2,3,4,5)]]:
    H=group(gens); even=all(sign(h)==1 for h in H); seen=set()
    for p in P:
        if p in seen:continue
        coset={mul(p,h) for h in H};seen.update(coset)
        check('Hodge',sum(sign(q) for q in coset)==(len(H)*sign(p) if even else 0))
    check('Hodge',len(seen)==720)
print(counts, 'total',sum(counts.values()))
