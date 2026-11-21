"""Exact physical collinear heat-flow control for R664/R665/R685.
Not a C2 bound or an Agda kernel receipt. Uses standard real Fourier helicity.
"""
import sympy as s
from itertools import product
I=s.I
z=s.zeros(3,1)
e=s.Matrix([1,0,0]); hp=s.Matrix([0,1,I]); hm=s.conjugate(hp)
N=5; K=2; k=(5,0,0)
t=s.symbols('t',nonnegative=True); nu=s.symbols('nu',positive=True)
base={(1,0,0):-5*hp,(2,0,0):6*hp,(3,0,0):hm,(4,0,0):hm}
base.update({tuple(-i for i in p):s.conjugate(v) for p,v in list(base.items())})
def norm2(p): return sum(i*i for i in p)
def u(p): return base.get(p,z)*s.exp(-nu*norm2(p)*t)
def helical(p,sign):
    if not norm2(p): return z
    v=u(p); return (v+sign*I*s.Matrix(p).cross(v)/s.sqrt(norm2(p)))/2
def simp(v): return v.applyfunc(s.simplify)
def work(a,b): return s.simplify(2*s.re((s.conjugate(a).T*b)[0]))
assert 2**K < max(map(abs,k)) <= 2**(K+1) and norm2(k)<3*4**K
for p,v in base.items():
    assert s.Matrix(p).dot(v)==0 and base[tuple(-i for i in p)]==s.conjugate(v)
for p,q in product(base,repeat=2):
    assert s.Matrix(q).dot(base[p])==0 # every advective interaction vanishes
M=z.copy(); B=z.copy(); n=0; active=[]
for p in product(range(-N,N+1),repeat=3):
    q=tuple(a-b for a,b in zip(k,p))
    if max(map(abs,q))>N: continue
    n+=1
    if p not in base or q not in base: continue
    a=simp(helical(p,1).cross(helical(q,-1)))
    if a==z: continue
    r=nu*(norm2(p)+norm2(q)); active.append((p,q,r,a)); M+=a; B+=r*a
assert n==726 and len(active)==2
M=simp(M); B=simp(B)
E=work(M,M)/2; W=work(M,B)
assert s.simplify(W+s.diff(E,t))==0
assert W.subs(t,0)==-56*nu
assert E.subs(t,0)==4
assert s.simplify(W.subs(t,s.log(2)/nu))>0
assert s.simplify(n*W.subs(t,0))==-40656*nu
print('PASS: complete fibre cardinality',n,'active cells',len(active))
print('M=',M.T,'weighted=',B.T)
print('E(0)=',E.subs(t,0),'weighted work(0)=',W.subs(t,0))
print('PASS: weighted work changes sign under exact unforced heat flow; W=-dE/dt')
