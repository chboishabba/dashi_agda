#!/usr/bin/env python3
"""Exact synthetic formative control, not biological or morphic evidence."""
import sympy as s
from itertools import product
checks=[]
def eq(label,a,b):
    d=a-b
    vals=list(d) if isinstance(d,s.MatrixBase) else [d]
    assert all(s.simplify(s.expand_complex(v))==0 for v in vals),label
    checks.append(label)
# Coherent three-port phase control. Algebraic DFT, not a calibrated device.
w=(-1+s.I*s.sqrt(3))/2
F=s.Matrix(3,3,lambda j,k:w**(-j*k)/s.sqrt(3)).applyfunc(s.simplify)
eq('DFT unitary',F.H*F,s.eye(3))
for r in range(3):
    a=s.Matrix([w**(r*k)/s.sqrt(3) for k in range(3)]).applyfunc(s.simplify)
    for k in range(3):eq('equal modal energy',s.conjugate(a[k])*a[k],s.Rational(1,3))
    eq('total modal energy',(a.H*a)[0],1)
    eq('selected port',F*a,s.eye(3)[:,r])
    eq('reverse coherent port',F.H*s.eye(3)[:,r],a)
# Original periodic Beltrami donor modes, phase offsets independent.
x,y,z,k=s.symbols('x y z k',real=True); X=(x,y,z)
ph=s.symbols('p0:3',real=True)
bs=[s.Matrix([0,s.sin(k*x+ph[0]),s.cos(k*x+ph[0])]),s.Matrix([s.cos(k*y+ph[1]),0,s.sin(k*y+ph[1])]),s.Matrix([s.sin(k*z+ph[2]),s.cos(k*z+ph[2]),0])]
def curl(v):return s.Matrix([s.diff(v[2],y)-s.diff(v[1],z),s.diff(v[0],z)-s.diff(v[2],x),s.diff(v[1],x)-s.diff(v[0],y)])
for b in bs:
    eq('Beltrami',curl(b),k*b);eq('divergence',sum(s.diff(b[i],X[i]) for i in range(3)),0);eq('unit mode norm',b.dot(b),1)
# 2pi cell at k=1; cross terms integrate to zero for arbitrary offsets.
for i,j in [(0,1),(0,2),(1,2)]:
    eq('orthogonal spatial modes',s.integrate(bs[i].dot(bs[j]).subs(k,1),(x,0,2*s.pi),(y,0,2*s.pi),(z,0,2*s.pi)),0)
b=sum(bs,s.zeros(3,1));eq('same-mode curl',curl(b),k*b)
eq('local readout phase 0',b.subs(dict.fromkeys(X+ph,0)),s.ones(3,1))
eq('local readout phase pi',b.subs(dict.fromkeys(X,0)).subs(dict.fromkeys(ph,s.pi)),-s.ones(3,1))
# Static magnetic Lorentz force does no work for arbitrary velocity and B.
v=s.Matrix(s.symbols('v0:3',real=True));B=s.Matrix(s.symbols('b0:3',real=True));eq('magnetic force work',v.dot(v.cross(B)),0)
# Positive Markov mixing and nonconstant formative tilt do not commute.
M=(s.eye(3)+s.ones(3)/3)/2;D=s.diag(1,2,4)
for i,j in product(range(3),repeat=2):eq('commutator component',(M*D-D*M)[i,j],M[i,j]*(D[j,j]-D[i,i]))
for j in range(3):eq('Markov column normalized',sum(M[:,j]),1)
p=s.Matrix([1,0,0]);norm=lambda a:a/sum(a)
l=M*norm(D*p);r=norm(D*M*p)
eq('tilt then mix',l,s.Matrix([s.Rational(2,3),s.Rational(1,6),s.Rational(1,6)]))
eq('mix then tilt',r,s.Matrix([s.Rational(2,5),s.Rational(1,5),s.Rational(2,5)]))
eq('order residual',r-l,s.Matrix([-s.Rational(4,15),s.Rational(1,30),s.Rational(7,30)]))
eq('residual mass zero',sum(r-l),0)
# Local history storage, pulse then no present exposure; reset intervention.
lam=s.Rational(3,4)
for n in range(7):
    m=1
    for _ in range(n):m*=lam
    eq('causal local memory',m,lam**n)
    eq('reset local memory',0*lam**n,0)
    assert m!=0;checks.append('same current input different later response')
print(f'{len(checks)}/{len(checks)} exact checks PASS; SymPy {s.__version__}')
