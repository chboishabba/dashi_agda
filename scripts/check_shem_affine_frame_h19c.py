from itertools import product
from collections import Counter
import sympy as sp
# Field coordinates encoded as a+3b+9c; t^3=t+1.
V=range(27)
def vec(x):return (x%3,x//3%3,x//9)
def enc(v):return sum((a%3)*3**i for i,a in enumerate(v))
add=[[enc(tuple(a+b for a,b in zip(vec(x),vec(y)))) for y in V] for x in V]
neg=[enc(tuple(-a for a in vec(x))) for x in V]
sub=[[add[x][neg[y]] for y in V] for x in V]
t=sp.symbols('t'); p=sp.Poly(t**3-t-1,t,modulus=3); assert p.is_irreducible
polys=[sp.Poly(sum(a*t**i for i,a in enumerate(vec(x))),t,modulus=3) for x in V]
mul=[[enc(tuple(int((polys[x]*polys[y]).rem(p).nth(i)) for i in range(3))) for y in V] for x in V]
inv=[0]+[mul[x].index(1) for x in range(1,27)]
ratio=lambda a,b,c:mul[sub[c][a]][inv[sub[b][a]]]
# Full reversible triple chart, with separate repeated-anchor stratum.
for a,b,c in product(V,repeat=3):
 d=sub[b][a]
 chart=(a,d,ratio(a,b,c) if d else sub[c][a])
 aa,dd,r=chart
 assert (aa,add[aa][dd],add[aa][mul[dd][r] if dd else r])==(a,b,c)
pows=[1]
for i in range(1,13):pows.append(mul[pows[-1]][3])
assert mul[pows[-1]][3]==1 and len(set(pows))==13
seed=(neg[1],neg[3],pows[5]); seeds=[seed,tuple(inv[x] for x in seed)]
ratios={ratio(*x) for x in seeds}; assert len(ratios)==2 and not ratios&{0,1}
actors=[(s,k) for s in range(1,27) for k in V]
def g(s,k,x):return add[mul[s][x]][k]
O={tuple(g(s,k,x) for x in seed) for seed in seeds for s,k in actors}
assert O=={(a,b,add[a][mul[r][sub[b][a]]]) for a,b in product(V,repeat=2) if a!=b for r in ratios}
for i in range(3):
 counts=Counter(tuple(x[j] for j in range(3) if j!=i) for x in O)
 assert len(counts)==702 and set(counts.values())=={2}
frames={(a,u):[mul[inv[u]][sub[x][a]] for x in V] for a in V for u in range(1,27)}
localI={(a,u):[add[a][mul[u][inv[z]]] for z in zs] for (a,u),zs in frames.items()}
frame_checks=inverse_checks=0
for s,k in actors:
 perm=[g(s,k,x) for x in V]
 for (a,u),zs in frames.items():
  target=(perm[a],mul[s][u]); zt=frames[target]; it=localI[target]; ia=localI[a,u]
  assert all(zt[perm[x]]==zs[x] for x in V); frame_checks+=27
  assert all(it[perm[x]]==perm[ia[x]] for x in V); inverse_checks+=27
C=list(product(range(3),range(8),range(-1,2),range(-1,2)))
def move(m,x):
 r,q,a,b=x
 if m&1 and r==1:q,a,b=7-q,-a,-b
 if m&2:r,q,a,b=2-r,7-q,-a,-b
 if m&4:q^=4
 return r,q,a,b
for x in C:
 for m,n in product(range(8),repeat=2):assert move(n,move(m,x))==move(n^m,x)
canon=lambda d:min(d,neg[d])
axes={canon(d) for d in range(1,27)};assert len(axes)==13
for a,u in frames:
 assert {canon(z) for z in frames[a,u] if z}==axes
 assert frames[a,u].count(0)==1
print({'triple_roundtrips':27**3,'degenerate_anchor':27**2,'distinct_anchor':27*26*27,'affine_ratio_codes':sorted(map(vec,ratios)),'orbit':len(O),'pair_fibres':702,'frame_checks':frame_checks,'anchored_inversion_checks':inverse_checks,'address_compositions':216*64,'frames':len(frames)})
