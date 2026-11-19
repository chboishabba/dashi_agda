"""Original L1 24-cell Wilson Taylor RG source integration (finite only).
Source: scripts/check_ym_original_L1_24cell_induced_rg_20261117.py.
Integer scaling of its exact quaternion/deficit enumeration; no continuum claim.
"""
from itertools import product
from collections import Counter
import sympy as s
V=[]
for a in range(4):
 for sign in (-1,1):
  q=[0]*4;q[a]=2*sign;V.append(tuple(q))
V+=list(product((-1,1),repeat=4)); idx={q:i for i,q in enumerate(V)}
def mul(q,r):
 a,b,c,d=q;e,f,g,h=r
 return tuple(x//2 for x in (a*e-b*f-c*g-d*h,a*f+b*e+c*h-d*g,a*g-b*h+c*e+d*f,a*h+b*g-c*f+d*e))
M=[[idx[mul(q,r)] for r in V] for q in V]
X=[[sum((q[a]*r[b]-q[b]*r[a])**2 for a,b in ((1,2),(1,3),(2,3))) for r in V] for q in V]
# X=8*deficit. Preserve all original six commutators and actual block.
fib=[Counter() for q in V]
for i,j,k,l in product(range(24),repeat=4):
 fib[M[i][j]][X[i][j]+X[i][k]+X[i][l]+X[j][k]+X[j][l]+X[k][l]]+=1
beta=s.Rational(1,96); raw=[]
for b,h in enumerate(fib):
 t=s.Rational(V[b][0],2)**2;n=sum(h.values());assert n==24**3
 m1=sum(s.Rational(d,8)*c for d,c in h.items())/n
 m2=sum(s.Rational(d,8)**2*c for d,c in h.items())/n
 assert m1==s.Rational(19,4)-t
 assert m2==s.Rational(4,3)*t*t-s.Rational(169,18)*t+s.Rational(230,9)
 raw.append(sum(c*(1-beta*s.Rational(d,8)+beta**2*s.Rational(d,8)**2/2) for d,c in h.items()))
Z=sum(raw);assert Z/24**4==s.Rational(140731,147456)
p=[w/Z for w in raw]; assert sum(p)==1 and min(p)>0
# Gauge invariant under simultaneous conjugation: trace of actual block.
f=[s.Rational(q[0],2) for q in V]
def E(k):return sum(w*x**k for w,x in zip(p,f))
mu=[E(k) for k in range(5)];assert mu[1]==mu[3]==0
# Compare exact fine weighted moments, with their coarse pullback.
for k in range(5):
 fine=sum(c*(1-beta*s.Rational(d,8)+beta**2*s.Rational(d,8)**2/2)*f[b]**k for b,h in enumerate(fib) for d,c in h.items())/Z
 assert fine==mu[k]
G=s.Matrix(3,3,lambda i,j:E(i+j)); u=s.Matrix(mu[:3]); C=G-u*u.T
assert C==s.Matrix(3,3,lambda i,j:sum(w*(x**i-mu[i])*(x**j-mu[j]) for w,x in zip(p,f)))
assert C.is_positive_semidefinite
kap=mu[4]-3*mu[2]**2
assert kap!=0
assert mu[2]!=s.Rational(1,4) # reject bare uniform coarse replacement
print('fine states',24**4,'fibres',len(fib),'Z',Z/24**4)
print('moments',mu,'centered ordinary Gram',C,'cumulant',kap)
print('PASS exact native finite RG pushforward / moments / ordinary Gram / nonzero cumulant; OS reflection, physical continuum and gap NOT TESTED')
