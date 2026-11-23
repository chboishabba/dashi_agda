from itertools import product
import sympy as s

def neg(p): return tuple(-x for x in p)
def rep(p): return p if next((x for x in p if x),0)>=0 else neg(p)
for d in (2,3):
 P=list(product((-1,0,1),repeat=d)); E=[(p,q) for p in P for q in P if p<q and sum(abs(x-y) for x,y in zip(p,q))==1]
 R=sorted(set(map(rep,P)))
 assert len(R)==(3**d+1)//2
 assert all((rep(p) if p==rep(p) else neg(rep(p)))==p for p in P)
 H=s.Matrix([[int(rep(p)==r) for r in R] for p in P])
 A=s.Matrix([[int(tuple(sorted((p,q))) in E) for q in P] for p in P])
 Q=s.Matrix([[sum(int(tuple(sorted((r,q))) in E) for q in P if rep(q)==t) for t in R] for r in R])
 assert A*H==H*Q
 print(d,len(P),len(E),len(R),len({tuple(sorted((rep(p),rep(q)))) for p,q in E}), 'equitable PASS')
 for k in range(1,2*d+1):
  weights=tuple((i%5)-2 for i in range(k)); B=list(product((-1,0,1),repeat=k))
  def val(b):return max(sum(w*(a!=x) for w,x in zip(weights,b)) for a in (-1,0,1))
  for b in B:
   occ={a:sum(w for w,x in zip(weights,b) if x==a) for a in (-1,0,1)}
   m=min(occ.values()); a=min(a for a in occ if occ[a]==m)
   assert val(b)==sum(weights)-m==sum(w*(a!=x) for w,x in zip(weights,b))==val(neg(b))
  print('arity',k,'raw',len(B),'quotient',len(set(map(rep,B))))
print('SymPy',s.__version__)
