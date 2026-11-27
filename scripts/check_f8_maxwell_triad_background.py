import sympy as s
b=s.symbols('b',positive=True); beta=s.sqrt(1+b*b); r=s.symbols('r', nonnegative=True)
rho=beta-1; p=-rho+b*b/(3*beta)
# radiation triad density r*b^4, residual canonical scalar kinetic
K=rho+p-4*r*b**4/3; V=(rho-p)/2-r*b**4/3
assert s.simplify(K/2+V+r*b**4-rho)==0
assert s.simplify(K/2-V+r*b**4/3-p)==0
assert s.simplify(b*s.diff(rho-r*b**4,b)-3*K)==0
# linear Maxwell triad stress variation, orthonormal E_i^a=e delta, B=0
u,v,w,x,y,z=s.symbols('u v w x y z'); D=s.Matrix([[u,x,y],[x,v,z],[y,z,w]]); e=s.symbols('e',positive=True)
I=s.eye(3); dr=e*s.trace(D); ds=e*s.trace(D)*I-2*e*D
assert s.expand(s.trace(ds)-dr)==0
P=s.Matrix([[u,x,y],[x,v,z],[y,z,-u-v]])
assert (ds.subs(w,-u-v)+2*e*P).applyfunc(s.expand)==s.zeros(3)
# canonical scalar background kinetic positive for r<1/(4 sqrt 2), b<=1
assert s.simplify(K-b*b*(1-4*r*b*b*beta)/(3*beta))==0
# target full background source energy bound from DEC for tracefree pi: rho+p+lambda_min >=0
print(s.__version__, '6 exact identities PASS')
