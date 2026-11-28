from itertools import product, permutations
from collections import Counter
import sympy as s

T = (-1, 0, 1)
P = list(product(T, repeat=2))
def bal(x): return (x + 1) % 3 - 1
def q(p): return p[0]**2 - p[1]**2
def rot(p): return (-p[1], p[0])
def d(a, b):
    assert len(a) == len(b)
    return next((len(a)-j for j,(x,y) in enumerate(zip(a,b)) if x != y), 0)
def shift(p, k, sign=1):
    z = list(p); z[-2+k] = bal(z[-2+k]+sign); return tuple(z)
def lift(p, t): return (t,) + p

x,y = s.symbols('x y', real=True)
S = s.Matrix([[0,-1],[1,0]])
M = S*s.Matrix([[1,1],[0,1]])
assert S**2 == -s.eye(2) and S**4 == s.eye(2) and M**3 == -s.eye(2)
assert S*s.Matrix([1,s.I]) == -s.I*s.Matrix([1,s.I])
assert s.expand(x*x+(s.I*y)**2-(x*x-y*y)) == 0
assert s.expand((x+y)*(x-y)-(x*x-y*y)) == 0
assert Counter(map(q,P)) == {-1:2,0:5,1:2}
assert {p for p in P if q(p)==0 and p!=(0,0)} == {(a,b) for a,b in product((-1,1),repeat=2)}
for p in P:
    assert q(rot(p)) == -q(p) and rot(rot(p)) == tuple(-v for v in p)
    u,v = p[0]+p[1],p[0]-p[1]
    assert (u+v,u-v) == (2*p[0],2*p[1])
for a,b,c in product(P,repeat=3):
    assert d(a,c) <= max(d(a,b),d(b,c))
    if d(a,b)<d(b,c): assert d(a,c)==d(b,c)
for a,b in product(P,repeat=2):
    assert d(a,b)==d(rot(a)[::-1],rot(b)[::-1])
assert d((0,0),(1,0)) != d(rot((0,0)),rot((1,0)))
assert q((1,1))==q((1,-1))==0 and q((2,0))!=0
faces=paths=squares=0
for n in range(4):
    for prefix in product(T,repeat=n):
        for p in P:
            a=prefix+p
            for sx,sy,t in product((-1,1),(-1,1),T):
                ops=(lambda z:shift(z,0,sx),lambda z:shift(z,1,sy),lambda z:lift(z,t))
                b,c=ops[0](a),ops[1](a)
                e=ops[1](b)
                assert e==ops[0](c)
                assert shift(b,0,-sx)==a and shift(c,1,-sy)==a
                assert d(a,e)==max(d(a,b),d(b,e))==max(d(a,c),d(c,e))==2
                assert d(lift(a,t),lift(e,t))==d(a,e)
                squares+=1
                for i,j in ((0,1),(0,2),(1,2)):
                    k=3-i-j
                    for z in (a,ops[k](a)):
                        assert ops[i](ops[j](z))==ops[j](ops[i](z)); faces+=1
                ends=[]
                for order in permutations(range(3)):
                    z=a
                    for i in order: z=ops[i](z)
                    ends.append(z); paths+=1
                assert len(set(ends))==1 and ends[0][1:]==e
# Gaussian Q_3(i): anisotropic residue norm; valuation of a+ib is min(v3(a),v3(b)).
assert all((a*a+b*b)%3!=0 for a,b in P if (a,b)!=(0,0))
print(f'PASS 729 prefix triangles, 81 transported rotation pairs, {squares} squares, {faces} cube faces, {paths} endpoint paths; signed/null/modular algebra and negative controls')
