"""H19d local exact replay: native Griess basis, dual incidence, ratio roles.
Classical finite field geometry; DASHI adapter, not creator cipher recognition.
"""
import sympy as s
from itertools import product,permutations
V=range(27)
vec=lambda x:(x%3,x//3%3,x//9)
enc=lambda v:sum(int(a)%3*3**i for i,a in enumerate(v))
add=[[enc([a+b for a,b in zip(vec(x),vec(y))]) for y in V] for x in V]
neg=[enc([-a for a in vec(x)]) for x in V]
sub=[[add[x][neg[y]] for y in V] for x in V]
t=s.symbols('t');p=s.Poly(t**3-t-1,t,modulus=3);assert p.is_irreducible
pol=[s.Poly(sum(a*t**i for i,a in enumerate(vec(x))),t,modulus=3) for x in V]
mul=[[enc([(pol[x]*pol[y]).rem(p).nth(i) for i in range(3)]) for y in V] for x in V]
inv=[0]+[mul[x].index(1) for x in range(1,27)]
M=s.Matrix([[1,1,0],[0,1,1],[1,1,1]])
v=s.Matrix([1,0,0]);B=s.Matrix.hstack(v,M*v,M**2*v).applyfunc(lambda a:a%3);Bi=B.inv_mod(3)
G=lambda x:enc(B*s.Matrix(vec(x)))
Gi=lambda x:enc(Bi*s.Matrix(vec(x)))
for x in V:
 assert Gi(G(x))==x and G(Gi(x))==x
 assert G(mul[3][x])==enc(M*s.Matrix(vec(G(x))))
 assert G(neg[x])==neg[G(x)]
for n,x in product(V,repeat=2):
 nn=Bi.T*s.Matrix(vec(n));xx=B*s.Matrix(vec(x))
 assert int(nn.dot(xx))%3==sum(a*b for a,b in zip(vec(n),vec(x)))%3
pw=[1]
for i in range(1,13):pw.append(mul[pw[-1]][3])
assert mul[pw[-1]][3]==1 and len(set(pw))==13
assert len({0}|{neg[x] for x in pw}|set(pw))==27
ratio=lambda a,b,c:mul[sub[c][a]][inv[sub[b][a]]]
seed=(neg[1],neg[3],pw[5])
ratios={ratio(*seed),ratio(*(inv[x] for x in seed))}
role=lambda r:{ratio(*p) for p in permutations((0,1,r))}
U=set.union(*(role(r) for r in ratios))
assert len(ratios)==2 and len(U)==12 and all(len(role(r))==6 for r in ratios)
for r in U:
 for a,b in product(V,repeat=2):
  if a==b:continue
  c=add[a][mul[r][sub[b][a]]]
  assert b==add[a][mul[inv[r]][sub[c][a]]]
  assert a==mul[inv[sub[1][r]]][sub[c][mul[r][b]]]
  assert ratio(a,b,c)==r
for a,b,c in product(V,repeat=3):
 d=sub[b][a];r=ratio(a,b,c) if d else sub[c][a]
 assert (a,add[a][d],add[a][mul[r][d] if d else r])==(a,b,c)
print({'B':B.tolist(),'B_inverse':Bi.tolist(),'det_mod3':int(B.det())%3,
 'signed_roundtrip':27,'singer':27,'sign':27,'normal_covariance':729,
 'ratio_sheets':[(r,vec(r),sorted(role(r))) for r in sorted(ratios)],
 'role_union':sorted(U),'role_inverse_checks':len(U)*702*3,'full_triple_chart':27**3})
