from itertools import product
from collections import Counter
from sympy import Matrix, GF, Poly, symbols, __version__
from sympy.polys.matrices import DomainMatrix
V=range(27)
x=symbols('x'); p=Poly(x**3-x-1,x,modulus=3); assert p.is_irreducible
d=lambda a:[a%3,a//3%3,a//9]
num=lambda v:sum((x%3)*3**i for i,x in enumerate(v))
A=[[num([x+y for x,y in zip(d(a),d(b))]) for b in V] for a in V]
D=[[num([x-y for x,y in zip(d(a),d(b))]) for b in V] for a in V]
P=[Poly(sum(v*x**i for i,v in enumerate(d(a))),x,modulus=3) for a in V]
M=[[num([int(q.nth(i)) for i in range(3)]) for b in V for q in [(P[a]*P[b]).rem(p)]] for a in V]
I=[0]+[M[a].index(1) for a in range(1,27)]
words=['ויסע מלאך האלהים ההלך לפני מחנה ישראל וילך מאחריהם ויסע עמוד הענן מפניהם ויעמד מאחריהם','ויבא בין מחנה מצרים ובין מחנה ישראל ויהי הענן והחשך ויאר את הלילה ולא קרב זה אל זה כל הלילה','ויט משה את ידו על הים ויולך יהוה את הים ברוח קדים עזה כל הלילה וישם את הים לחרבה ויבקעו המים']
glyphs='אבגדהוזחטיכלמנסעפצקרשתךםןףץ'; enc={}
for i,g in enumerate(glyphs):
 t=i//9; u=i%3; v=i%9//3; enc[g]=num([t,t+u,t+v])
rows=[[enc[g] for g in w.replace(' ','')] for w in words]; rows[1].reverse(); a,b,c=rows
assert all(len(r)==72 for r in rows)
end=[i==len(w)-1 for w in words[2].split() for i in range(len(w))]
left=set(V)-{0,1}; orb=[]
while left:
 r=min(left); o={r,I[r],D[1][r],I[D[1][r]],M[r][I[D[r][1]]],M[D[r][1]][I[r]]}; orb.append(o); left-=o
lookup={r:i for i,o in enumerate(orb) for r in o}
def sheet(a,b,c):
 if a==b:return ('equal',a==c)
 if c==a:return 'first'
 if c==b:return 'second'
 return lookup[M[D[c][a]][I[D[b][a]]]]
rev={v:g for g,v in enc.items()}; final=set('ךםןףץ'); medial=set('כמנפצ')
domains=[{v for v in V if (i not in (0,36) or v==c[i]) and rev[v] not in (medial if end[i] else final) and sheet(a[i],b[i],v)==sheet(a[i],b[i],c[i])} for i in range(72)]
idx=list(product(range(3),range(4),range(6)))
unit=lambda t:[int(s==t) for s in idx]
J=lambda g,h,k:24*g+6*h+k
margins=[[int((a,b)==(g,h)) for a,b,c in idx] for g,h in product(range(3),range(4))]+[[int(c==k) for a,b,c in idx] for k in range(6)]
mix=[[a-b-c+d for a,b,c,d in zip(unit((g,h,k)),unit((g,h+1,k)),unit((g,h,k+1)),unit((g,h+1,k+1)))] for g,h,k in product(range(3),range(3),range(5))]
anchors=[unit(idx[i]) for i in (0,36)]
rank=lambda r:DomainMatrix.from_Matrix(Matrix(r)).convert_to(GF(3)).rank()
assert [rank(r) for r in (margins,mix,margins+mix,margins+mix+anchors)]==[17,45,53,55]
# Independent enumeration of additive residuals; anchor row gauge u0=0.
from functools import reduce
from operator import mul
addsum=lambda vs:reduce(lambda a,b:A[a][b],vs,0)
sol=[]; no_margins=[]
for g in range(3):
 out=[]; total=0; valid=0
 for tail in product(V,repeat=3):
  u=(0,)+tail
  vs=[set.intersection(*[{D[D[y][c[J(g,h,k)]]][u[h]] for y in domains[J(g,h,k)]} for h in range(4)]) for k in range(6)]
  if not all(vs):continue
  valid+=1; total+=reduce(mul,map(len,vs),1)
  for v in product(*vs):
   if addsum(v)==0:out.append(tuple(A[addsum(u)][x] for x in v))
 sol.append(out); no_margins.append(total)
 print('group',g,'valid u',valid,'without margins',total,'with row sums',len(out))
count=sum(Counter(sol[2])[tuple(D[0][A[x][y]] for x,y in zip(s,t))] for s,t in product(sol[0],sol[1]))
assert count==1
print('SymPy',__version__,'ranks PASS, exact combined oracle count',count,'without margins',reduce(mul,no_margins,1))
