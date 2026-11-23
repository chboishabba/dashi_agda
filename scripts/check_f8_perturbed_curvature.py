"""AdS5 polarized TT metric slice, NOT the full F8 nonlinear carrier.
Reuse YM commutator convention and NS signed-work ledger; no Einstein closure.
Coordinates (T,x,y,w,z), AdS radius L, h(T,x,z) arbitrary.
"""
import sympy as s
from itertools import combinations
T,x,y,w,z,L=s.symbols('T x y w z L', real=True, nonzero=True)
coords=(T,x,y,w,z); h=s.Function('h')(T,x,z)
eta=s.diag(-1,1,1,1,1); g=L**2/z**2*s.diag(-1,1,s.exp(2*h),s.exp(-2*h),1)
e=L/z*s.diag(1,1,s.exp(h),s.exp(-h),1); ei=e.inv(); gi=g.inv()
zero=s.zeros(5); simp=lambda A:A.applyfunc(s.simplify)
assert simp(e.T*eta*e-g)==zero
Gamma=[s.Matrix(5,5,lambda a,b:s.simplify(sum(gi[a,c]*(s.diff(g[c,b],coords[m])+s.diff(g[c,m],coords[b])-s.diff(g[m,b],coords[c]))/2 for c in range(5)))) for m in range(5)]
# Tetrad postulate, induced torsion-free metric connection.
Omega=[simp(e*Gamma[m]*ei-e.diff(coords[m])*ei) for m in range(5)]
for m in range(5):
 assert simp(Omega[m].T*eta+eta*Omega[m])==zero
for m,n in combinations(range(5),2):
 assert simp(e[:,n].diff(coords[m])-e[:,m].diff(coords[n])+Omega[m]*e[:,n]-Omega[n]*e[:,m])==s.zeros(5,1)
bar=[a.subs(h,0).doit() for a in Omega]; delta=[a-b for a,b in zip(Omega,bar)]
comm=lambda a,b:a*b-b*a
R={}
for m,n in combinations(range(5),2):
 cur=simp(Gamma[n].diff(coords[m])-Gamma[m].diff(coords[n])+comm(Gamma[m],Gamma[n]));R[m,n]=cur
 spin=simp(Omega[n].diff(coords[m])-Omega[m].diff(coords[n])+comm(Omega[m],Omega[n]))
 bg=bar[n].diff(coords[m])-bar[m].diff(coords[n])+comm(bar[m],bar[n])
 lin=delta[n].diff(coords[m])-delta[m].diff(coords[n])+comm(bar[m],delta[n])+comm(delta[m],bar[n])
 assert simp(spin-bg-lin-comm(delta[m],delta[n]))==zero
 assert simp(spin-e*cur*ei)==zero
ric=simp(s.Matrix(5,5,lambda b,n:sum((R[a,n][a,b] if a<n else -R[n,a][a,b] if a>n else 0) for a in range(5))))
E=simp(ric+4*g/L**2)
wave=-h.diff(T,2)+h.diff(x,2)+h.diff(z,2)-3*h.diff(z)/z
expected=s.zeros(5)
for a in (0,1,4):
 for b in (0,1,4):expected[a,b]=-2*h.diff(coords[a])*h.diff(coords[b])
expected[2,2]=-s.exp(2*h)*wave;expected[3,3]=s.exp(-2*h)*wave
assert simp(E-expected)==zero
assert E[0,0]!=0
print('PASS: 5 metric compatibility, 10 torsion, 10 curvature split, 10 frame transport; exact Ricci residual')
print('Base residual = -2 dh tensor dh; fiber residual = +/- exp(+/-2h) times AdS wave operator')
print('Linear TT wave alone does not solve nonlinear vacuum Einstein in this restricted metric.')
