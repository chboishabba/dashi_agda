"""Second-order bulk Einstein source on AdS5; no junction or nonlinear evolution.
F8 #1527 original scalar TT readout; #1530 polarized curvature predecessor.
Standard metric connection variation, not a new GR theorem.
"""
import sympy as s
T,x,y,w,z=s.symbols('T x y w z', real=True); X=(T,x,y,w,z); N=range(5)
eta=s.diag(-1,1,1,1,1); g=eta/z**2; inv=z**2*eta
Z=s.zeros(5); simp=lambda A:A.applyfunc(s.expand)
# Gamma[m][a,b] = Gamma^a_mb for unit AdS radius.
B=[s.Matrix(5,5,lambda a,b: (-int(a==m)*int(b==4)-int(a==b)*int(m==4)+eta[m,b]*eta[a,4])/z) for m in N]
def cov(H,m):return H.diff(X[m])-B[m].T*H-H*B[m]
def connection(H):
 D=[cov(H,m) for m in N]
 return [simp(s.Matrix(5,5,lambda a,b:sum(inv[a,c]*(D[m][c,b]+D[b][c,m]-D[c][m,b])/2 for c in N))) for m in N]
def dc(C,m,n):return C[n].diff(X[m])+B[m]*C[n]-C[n]*B[m]-sum((B[m][k,n]*C[k] for k in N),Z)
def ric(C):
 return simp(s.Matrix(5,5,lambda b,n:sum(dc(C,a,n)[a,b]-dc(C,n,a)[a,b] for a in N)))
def linear(H):return simp(ric(connection(H))+4*H)
def quadratic(H):
 C=connection(H); D=[simp(-inv*H*A) for A in C]
 Q=s.Matrix(5,5,lambda b,n:sum((C[a]*C[n]-C[n]*C[a])[a,b] for a in N))
 return simp(ric(D)+Q)
def divergence(A):
 D=[cov(A,m) for m in N];return s.Matrix([s.expand(sum(inv[a,k]*D[a][k,n] for a in N for k in N)) for n in N])
def trace_reverse(A):return simp(A-g*s.trace(inv*A)/2)
# Three nontrivial TT waves, distinct directions and a normal-dependent mode.
a,b,c=s.symbols('a b c',real=True)
H1=s.diag(0,0,2*(T-x)**2,-2*(T-x)**2,0)/z**2
H2=s.diag(0,2*(T-y)**2,0,-2*(T-y)**2,0)/z**2
H3=s.diag(0,2*z**4,-2*z**4,0,0)/z**2
H=a*H1+b*H2+c*H3
assert s.expand(s.trace(inv*H))==0 and divergence(H)==s.zeros(5,1)
assert linear(H)==Z
Q=quadratic(H); assert Q==Q.T and Q!=Z
assert divergence(trace_reverse(Q))==s.zeros(5,1)
for i,j in [(a,b),(a,c),(b,c)]:
 cross=Q.diff(i,j); assert cross!=Z
 assert divergence(trace_reverse(cross))==s.zeros(5,1)
# Match previous exact exponential polarized ansatz: metric epsilon^2 term.
f=(T-x)**2; Hexp=s.diag(0,0,2*f*f,2*f*f,0)/z**2
assert simp(quadratic(H1)+linear(Hexp)+2*s.Matrix([f.diff(t) for t in X])*s.Matrix([f.diff(t) for t in X]).T)==Z
print('PASS: full 5x5 quadratic source, TT linear equation, trace-reversed Bianchi, 3 mixed interactions, polarized predecessor parity')
print('mixed source entries (a b, a c, b c):',*[sum(v!=0 for v in Q.diff(i,j)) for i,j in [(a,b),(a,c),(b,c)]])
# Compact local TT differential projector, y-axis seed. Polynomial radial checks.
xyz=(x,y,w); r2=x*x+y*y+w*w
lap=lambda f:sum(f.diff(v,2) for v in xyz)
def P(i,j,f):return (lap(f) if i==j else 0)-f.diff(xyz[i],xyz[j])
for n in (2,3,4,5):
 f=r2**n; A=s.Matrix(3,3,lambda i,j:s.expand(P(i,1,P(j,1,f))-P(i,2,P(j,2,f))-P(i,j,P(1,1,f)-P(2,2,f))/2))
 assert s.expand(s.trace(A))==0
 assert all(s.expand(sum(A[i,j].diff(xyz[i]) for i in range(3)))==0 for j in range(3))
print('PASS: four radial polynomial full spatial TT projector checks; not yet F8 source normalization or evolution parity')
# Original F8 yy source profiles: check all three Legendre coefficients
# using arbitrary radial jets (f is a function of radius squared).
r,mu,u=s.symbols('r mu u',real=True,positive=True); F=s.Function('F')
f=F(r2); yy=s.expand(P(1,1,P(1,1,f))-P(1,2,P(1,2,f))-P(1,1,P(1,1,f)-P(2,2,f))/2)
# Average azimuth about original x receiver axis.
# Replace radial jet arguments before angular substitution.
jet=s.symbols('j0:5')
for k in range(4,0,-1):
 yy=yy.subs(s.Subs(s.Derivative(F(u),(u,k)),u,r2),jet[k])
# SymPy represents derivatives with direct composition or Subs; normalize.
for atom in yy.atoms(s.Subs):
 if isinstance(atom.expr,s.Derivative) and atom.expr.expr.func==F:
  yy=yy.xreplace({atom:jet[sum(c for _,c in atom.expr.variable_count)]})
for atom in yy.atoms(s.Derivative):
 if atom.expr.func==F: yy=yy.xreplace({atom:jet[sum(c for _,c in atom.variable_count)]})
phi=s.symbols("phi",real=True)
yy=s.expand(yy.subs({x:r*mu,y:r*s.sqrt(1-mu**2)*s.cos(phi),w:r*s.sqrt(1-mu**2)*s.sin(phi)}, simultaneous=True))
yy=s.expand(s.integrate(yy,(phi,0,2*s.pi))/(2*s.pi))
# f_rad(r)=F(r^2); radial derivatives expressed in identical jets.
d=[None]+[s.diff(F(r*r),r,k) for k in range(1,5)]
for k in range(1,5):
 for atom in d[k].atoms(s.Subs):
  if isinstance(atom.expr,s.Derivative) and atom.expr.expr.func==F:
   d[k]=d[k].xreplace({atom:jet[sum(c for _,c in atom.expr.variable_count)]})
 for atom in d[k].atoms(s.Derivative):
  if atom.expr.func==F:d[k]=d[k].xreplace({atom:jet[sum(c for _,c in atom.variable_count)]})
expected=[s.Rational(2,5)*(d[4]+4*d[3]/r),s.Rational(4,7)*(d[4]+d[3]/r-6*d[2]/r**2+6*d[1]/r**3),s.Rational(1,35)*(d[4]-6*d[3]/r+15*d[2]/r**2-15*d[1]/r**3)]
actual=[s.expand((2*l+1)*s.integrate(yy*s.legendre(l,mu),(mu,-1,1))/2) for l in (0,2,4)]
assert all(s.simplify(a-b)==0 for a,b in zip(actual,expected))
assert s.expand(yy-sum(a*s.legendre(l,mu) for a,l in zip(actual,(0,2,4))))==0
print("PASS: original Q=diag(0,1,-1), x-axis azimuth-average yy profiles l=0,2,4, arbitrary radial jets")
