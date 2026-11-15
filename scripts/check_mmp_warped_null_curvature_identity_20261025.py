#!/usr/bin/env python3
"""Independent coordinate geometry for static spherical warped line:
 ds²=-N(x)² dt²+dx²+r(x)²(dtheta²+sin(theta)² dphi²).
No assumption that any quantum source supports this metric.
"""
import json
import sympy as s
x,tt,th,ph=s.symbols('x t theta phi',real=True)
N=s.Function('N')(x)
r=s.Function('r')(x)
coords=[tt,x,th,ph]
g=s.diag(-N**2,1,r**2,r**2*s.sin(th)**2)
gi=s.diag(-1/N**2,1,1/r**2,1/(r**2*s.sin(th)**2))
Gm=[[[s.S.Zero for _ in range(4)] for _ in range(4)] for _ in range(4)]
for a in range(4):
 for b in range(4):
  for c in range(4):
   Gm[a][b][c]=s.simplify(sum(gi[a,d]*(s.diff(g[d,c],coords[b])+s.diff(g[d,b],coords[c])-s.diff(g[b,c],coords[d]))/2 for d in range(4)))
Ric=s.zeros(4)
for a in range(4):
 for b in range(4):
  Ric[a,b]=s.trigsimp(s.simplify(sum(s.diff(Gm[c][a][b],coords[c])-s.diff(Gm[c][a][c],coords[b])+sum(Gm[c][c][d]*Gm[d][a][b]-Gm[c][b][d]*Gm[d][a][c] for d in range(4)) for c in range(4))))
Rscalar=s.simplify(sum(gi[a,a]*Ric[a,a] for a in range(4)))
Ein=s.simplify(Ric-Rscalar*g/2)
Gkk=s.factor(Ein[0,0]/N**2+Ein[1,1])
expected=s.factor(2*(s.diff(N,x)*s.diff(r,x)/N-s.diff(r,x,2))/r)
assert s.simplify(Gkk-expected)==0
for row in range(4):
 for col in range(4):
  if row!=col:assert s.simplify(Ein[row,col])==0
product={N:s.Integer(1),r:s.symbols('R',positive=True)}
val=[s.simplify(Ein[i,i].subs(product, simultaneous=True)) for i in range(4)]
RR=product[r]
assert s.simplify(val[0]-1/RR**2)==0
assert s.simplify(val[1]+1/RR**2)==0
assert s.simplify(val[2])==s.simplify(val[3])==0
assert s.simplify(Rscalar.subs(product,simultaneous=True)-2/RR**2)==0
print(json.dumps({'warped_null_Einstein_orthonormal':str(Gkk), 'product_Einstein_diagonal':list(map(str,val)), 'product_scalar_curvature':str(s.simplify(Rscalar.subs(product,simultaneous=True).doit())), 'invariant':'G_kk=-2*(rpp-(Nprime/N)*rprime)/r; at throat rprime=0, G_kk=-2*rpp/r'},indent=2))
print('PASS independent tensorial curved geometry calculation matches null identity and flat x S2 obstruction')
