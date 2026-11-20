import sympy as s
x,B,g,D=s.symbols('x B gamma Delta',real=True)
V=D*x*x/2+g*x**4/4-B*x
inv=B/x-g*x*x
assert s.simplify(s.diff(V,x).subs(D,inv))==0
assert s.simplify(s.diff(V,x,2).subs(D,inv)-(B/x+2*g*x*x))==0
assert s.simplify(V.subs(D,inv)+B*x/2+g*x**4/4)==0
for target in (-1,1):
    # normalized exterior correction X; same positive ambient bias
    b=s.Rational(1,10); gamma=s.Integer(1); X=s.Integer(target)
    delta=inv.subs({B:b,g:gamma,x:X})
    pot=V.subs({D:delta,B:b,g:gamma}); roots=s.solve(s.diff(pot,x),x)
    print('target',target,'Delta',delta,'curvature',s.diff(pot,x,2).subs(x,X),'energy',pot.subs(x,X),'stationary',[(str(r),float(pot.subs(x,r))) for r in roots])
    assert s.diff(pot,x,2).subs(x,X)>0
# periodic control exact balance with gradient eliminated quasistatically
v,dd,db,gg,M,eta=s.symbols('v dDelta dB dGamma M eta',real=True)
acc=(B-D*x-g*x**3-eta*v)/M
assert s.expand(M*v*acc+s.diff(V,x)*v+eta*v*v)==0
print('PASS nonlinear inverse, Hessian, equilibrium energy, signed branches and damping ledger')
