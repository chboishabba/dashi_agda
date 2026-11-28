from sympy import Poly, symbols, __version__
from itertools import product
from collections import Counter
x=symbols('x'); p=Poly(x**3-x-1,x,modulus=3); assert p.is_irreducible
V=list(range(27)); ds=lambda a:[a%3,a//3%3,a//9]; num=lambda a:sum((v%3)*3**i for i,v in enumerate(a))
A=[[num([u+v for u,v in zip(ds(a),ds(b))]) for b in V] for a in V]
D=[[num([u-v for u,v in zip(ds(a),ds(b))]) for b in V] for a in V]
P=[Poly(sum(v*x**i for i,v in enumerate(ds(a))),x,modulus=3) for a in V]
M=[[num([int(q.nth(i)) for i in range(3)]) for b in V for q in [(P[a]*P[b]).rem(p)]] for a in V]
I=[0]+[M[a].index(1) for a in V[1:]]; F=[M[a][M[a][a]] for a in V]; F2=[F[a] for a in F]
assert all(F[F2[a]]==a for a in V)
assert [a for a in V if F[a]==a]==[0,1,2]
def span(bs):
 out={0}
 for b in bs:out={A[x][M[k][b]] for x,k in product(out,range(3))}
 return out
linear=[]
for u,v in product(V,repeat=2):
 if len(span([1,u,v]))!=27:continue
 linear.append([A[A[M[a][1]][M[b][u]]][M[c][v]] for a,b,c in map(ds,V)])
assert len(linear)==432 and all(len(set(g))==27 and g[0]==0 and g[1]==1 for g in linear)
assert {y for y in (g[3] for g in linear)}==set(V)-{0,1,2}
assert [a for a in V if all(g[a]==a for g in linear)]==[0,1,2]
# Unique Frobenius orientation with an independently observed non-base-field anchor.
checks=0
for a,b,c in product(V,repeat=3):
 if a==b:continue
 u=D[b][a]; r=M[I[u]][D[c][a]]
 if r in (0,1,2):continue
 orb=[r,F[r],F2[r]]; assert len(set(orb))==3
 k=orb.index(min(orb)); maps=[V,F,F2]; enc=maps[k]; dec=maps[(-k)%3]
 for y in V:
  z=enc[M[I[u]][D[y][a]]]; assert A[a][M[u][dec[z]]]==y
  checks+=1
print('SymPy',__version__,'432 linear stabilizer permutations; fixed 0,1,2; off-line orbit 24; Frobenius fixed 0,1,2; canonical orientation roundtrips',checks)
