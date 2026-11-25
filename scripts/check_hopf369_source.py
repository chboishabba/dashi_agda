#!/usr/bin/env python3
"""Classical Hopf/Whitehead reference, DASHI source-specific cross-consumer audit.
Not AFZ/KN stationarity, NS evolution, Wilson measure or Agda acceptance.
"""
import sympy as s
x,y,z=s.symbols('x y z', real=True)
X=(x,y,z); D=1+x*x+y*y+z*z
q=s.Matrix([2*x,2*y,2*z,D-2])/D
a,b,c,d=q; v=s.Matrix([b,c,d])
f=lambda w:s.factor(s.cancel(w))
clean=lambda w:w.applyfunc(f)
grad=lambda w:s.Matrix([s.diff(w,t) for t in X])
def curl(w):
    return clean(s.Matrix([s.diff(w[2],y)-s.diff(w[1],z),s.diff(w[0],z)-s.diff(w[2],x),s.diff(w[1],x)-s.diff(w[0],y)]))
def div(w):
    return f(sum(s.diff(w[i],X[i]) for i in range(3)))
checks=[]
def eq(name,l,r):
    assert (clean(l-r)==s.zeros(*l.shape) if isinstance(l,s.MatrixBase) else f(l-r)==0),name
    checks.append(name)
A=clean(a*grad(b)-b*grad(a)+c*grad(d)-d*grad(c)); B=curl(A)
n=clean(s.Matrix([2*(a*c+b*d),2*(b*c-a*d),a*a+b*b-c*c-d*d]))
eq('unit S3',q.dot(q),1)
eq('unit S2',n.dot(n),1)
for i,j,k in [(0,1,2),(1,2,0),(2,0,1)]:
    eq('area pullback '+str(i),n.dot(n.diff(X[j]).cross(n.diff(X[k]))),-2*B[i])
eq('curvature closed',div(B),0)
eq('potential not Coulomb gauge',div(A),4*z/D**2)
eq('contact norm',A.dot(A),4/D**2)
eq('curvature norm',B.dot(B),64/D**4)
eq('helicity density',A.dot(B),16/D**3)
r=s.symbols('r',positive=True)
def radial(p,c):
    return s.integrate(4*s.pi*r*r*c/(1+r*r)**p,(r,0,s.oo))
eq('Hopf charge',radial(3,16)/(4*s.pi**2),1)
# Orientation-reversing pullback of the one-form; curl is axial.
S=s.diag(-1,1,1); Ar=clean(S*A.subs(x,-x)); Br=curl(Ar)
eq('mirror curvature',Br,-S*B.subs(x,-x))
eq('mirror charge density',Ar.dot(Br),-16/D**3)
# NS initial velocity B, not A; Euclidean kinetic helicity is distinct.
C=curl(B)
eq('NS kinetic helicity density',B.dot(C),256/D**5)
eq('NS kinetic helicity',radial(5,256),20*s.pi**2)
eq('NS energy',radial(4,32),4*s.pi**2)
eq('non-gradient Lamb vector at witness',curl(B.cross(C)).subs(dict(zip(X,(1,0,0)))),s.Matrix([-4,0,0]))
# Right Maurer-Cartan R=dq q^-1; A is its first component.
R=[clean(a*v.diff(t)-s.diff(a,t)*v+v.cross(v.diff(t))) for t in X]
eq('Cartan projection',s.Matrix([w[0] for w in R]),A)
for i,j in [(0,1),(0,2),(1,2)]:
    eq('flat full connection '+str((i,j)),R[j].diff(X[i])-R[i].diff(X[j]),2*R[i].cross(R[j]))
assert B.subs(dict(zip(X,(0,0,0))))!=s.zeros(3,1)
checks.append('nonflat projected curvature')
print(f'{len(checks)}/{len(checks)} PASS; SymPy {s.__version__}; Q=1, mirror Q=-1, E_NS=4*pi^2, H_NS=20*pi^2')
