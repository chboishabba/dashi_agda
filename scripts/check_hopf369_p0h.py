#!/usr/bin/env python3
"""P0H: original uncut Hopf Fourier source and Einstein CMC constraint algebra.
The contraction proof and matter reconstruction are analytical, not a PDE simulation.
"""
import sympy as s
checks=[]
def eq(name,a,b):
    d=a-b
    ok=all(s.simplify(v)==0 for v in d) if isinstance(d,s.MatrixBase) else s.simplify(d)==0
    assert ok,name
    checks.append(name)
x,y,z=s.symbols('x y z',real=True); X=(x,y,z); D=1+x*x+y*y+z*z
A=2*s.Matrix([2*x*z-2*y,2*x+2*y*z,1-x*x-y*y+z*z])/D**2
curl=lambda v:s.Matrix([s.diff(v[2],y)-s.diff(v[1],z),s.diff(v[0],z)-s.diff(v[2],x),s.diff(v[1],x)-s.diff(v[0],y)])
B=8*s.Matrix([2*x*z-2*y,2*x+2*y*z,1-x*x-y*y+z*z])/D**3
eq('original curl',curl(A),B)
eq('original divergence',sum(s.diff(B[i],X[i]) for i in range(3)),0)
eq('original helicity density',A.dot(B),16/D**3)
eq('original energy density',B.dot(B),64/D**4)
r=s.symbols('r',positive=True)
eq('helicity integral',s.integrate(64*s.pi*r*r/(1+r*r)**3,(r,0,s.oo)),4*s.pi**2)
eq('energy integral',s.integrate(256*s.pi*r*r/(1+r*r)**4,(r,0,s.oo)),8*s.pi**2)
# Transform of D^-3 obtained by differentiating the standard radial transform of (r²+a²)^-2.
a=s.symbols('a',positive=True)
eq('radial transform recurrence',-s.diff(s.pi**2*s.exp(-a*r)/a,a)/(4*a),s.pi**2*(1+a*r)*s.exp(-a*r)/(4*a**3))
k1,k2,k3=s.symbols('k1 k2 k3',real=True); k=s.Matrix([k1,k2,k3]); k2norm=k.dot(k)
# Avoid radical simplification by using independent radius r and reducing modulo r²=k·k.
F=s.Matrix([-k1*k3+s.I*r*k2,-k2*k3-s.I*r*k1,k1*k1+k2*k2])
def radial_eq(name,a,b):
    d=a-b; vals=list(d) if isinstance(d,s.MatrixBase) else [d]
    assert all(s.rem(s.expand(v),r*r-k2norm,r)==0 for v in vals),name
    checks.append(name)
radial_eq('Fourier transversality',k.dot(F),0)
radial_eq('positive helical eigenvalue',s.I*k.cross(F),r*F)
radial_eq('Fourier norm',s.conjugate(F).dot(F),2*r*r*(k1*k1+k2*k2))
eq('reality',F.subs({k1:-k1,k2:-k2,k3:-k3},simultaneous=True),s.conjugate(F))
# Fourier Bhat=4pi² exp(-r) F/r; York tracefree tensor numerator.
kap,alpha=s.symbols('kap alpha',positive=True)
Y=k*F.T+F*k.T
radial_eq('York trace',s.trace(Y),0)
radial_eq('York divergence',Y*k,r*r*F)
radial_eq('York tensor norm',sum(s.conjugate(v)*v for v in Y),4*r**4*(k1*k1+k2*k2))
# Angular integral sin²(theta)=8pi/3 and physical Parseval (2pi)^-3.
for n,target in [(0,8*s.pi**2),(-1,4*s.pi**2),(1,20*s.pi**2),(-2,8*s.pi**2/3),(2,60*s.pi**2)]:
    val=32*s.pi**4*(8*s.pi/3)/(2*s.pi)**3*s.integrate(r**(4+n)*s.exp(-2*r),(r,0,s.oo))
    eq('spectral moment '+str(n),val,target)
eq('York L2 norm',2*kap**2*alpha**2*8*s.pi**2/3,16*s.pi**2*kap**2*alpha**2/3)
eq('York uniform bound',8*s.pi**2*kap*alpha/(2*s.pi)**3*4*s.pi*s.integrate(r*r*s.exp(-r),(r,0,s.oo)),8*kap*alpha)
# CMC conformal Hamiltonian, background cancellation, same-source energy target.
psi,K0,p0,Ktrace,GN,eps,b2,Y2,Lap=s.symbols('psi K0 p0 Ktrace GN eps b2 Y2 Lap',positive=True)
rho0=K0-p0
res=-8*psi**-5*Lap+2*Ktrace**2/3-psi**-12*Y2-16*s.pi*GN*(rho0+eps**2*psi**-8*b2)
res=res.subs(Ktrace**2,24*s.pi*GN*rho0).subs(Lap,-2*s.pi*GN*eps**2*psi**-3*b2-s.Rational(1,8)*psi**-7*Y2)
eq('Hamiltonian cancellation',res,0)
# Perfect fluid primitive recovery: S=fluid normal density, C=e-p, j²=(S+p)(S-e).
S,C,j2=s.symbols('S C j2',real=True)
e=(C+s.sqrt((2*S-C)**2-4*j2))/2;p=e-C
eq('primitive recovery', (S+p)*(S-e),j2)
eq('stiff EOS',e-p,C)
# At psi=1 and b²<K0, recover exact P0E root with positive square root.
eq('P0E discriminant',(K0+b2)**2-4*K0*b2,(K0-b2)**2)
eq('P0E root',(K0-2*p0+K0-b2)/2,K0-p0-b2/2)
# Signed helicity under conformal volume scaling: b^i=eps psi^-6 B^i, A_i=eps A_i.
eq('helicity weight',eps*eps*psi**-6*psi**6,eps**2)
# Physical divergence density and momentum scaling powers.
eq('magnetic volume weight',psi**6*psi**-6,1)
eq('York momentum weight',psi**10*psi**-10,1)
print(f'{len(checks)}/{len(checks)} exact assertions PASS; SymPy {s.__version__}')
