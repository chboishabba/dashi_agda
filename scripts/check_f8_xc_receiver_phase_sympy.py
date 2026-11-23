"""F8 XC: original receiver cubic-stencil phase audit (geometry only).
SymPy proves exact quartic interpolation value/derivative residuals; evaluates
the original near/far physical receiver against A/C grid positions.
This does NOT compute original evolved field derivatives or Weyl error.
"""
import json,math
import sympy as S
q=S.symbols("q",real=True)
nodes=(-1,0,1,2)
P=S.prod(q-j for j in nodes)
weights=[S.prod((q-m)/(n-m) for m in nodes if m!=n) for n in nodes]
interp=S.expand(sum(weights[i]*S.Integer(nodes[i])**4 for i in range(4)))
assert S.simplify(q**4-interp-P)==0
E0=P/S.factorial(4)
E1=S.diff(E0,q)
E2=S.diff(E1,q)
assert S.simplify(E2-(q*q/S.Integer(2)-q/S.Integer(2)-S.Rational(1,12)))==0
T=S.symbols("T",positive=True)
F=S.asinh(T)-S.sqrt(1+T*T)/T
assert S.simplify(S.diff(F,T)-S.sqrt(1+T*T)/T**2)==0
t=S.Integer(12)
span=(F.subs(T,t)-F.subs(T,1)).evalf(40)
bulk=S.sqrt(span**2-(1-S.Rational(1,12))**2)
rows=[]
for location,rx in (("near",bulk-S.Rational(12,1000)),("far",bulk+S.Rational(1,10))):
    for h in (S.Rational(8,1000),S.Rational(6,1000)):
        x=rx/h
        j=int(S.floor(x))
        phase=(x-j).evalf(40)
        assert 0<=phase<1
        d1=(h**3*E1.subs(q,phase)).evalf(40)
        d2=(h**2*E2.subs(q,phase)).evalf(40)
        per_mode={}
        for ell in (0,2,4):
            # Only quartic polynomial test v(r); not actual evolved field v.
            lead=((rx/S.Rational(4,100))**ell *
                  (d2+(2*ell+2)*d1/rx)).evalf(30)
            per_mode[str(ell)]=float(lead)
        rows.append(dict(location=location,dr=float(h),cell=j,
                         fractional_position=float(phase),
                         quartic_second_derivative_error_coefficient=float(d2),
                         quartic_Delta3_error_coefficients=per_mode))
near=[r for r in rows if r["location"]=="near"]
assert near[0]["cell"]==317 and near[1]["cell"]==422
assert abs(near[0]["quartic_second_derivative_error_coefficient"] /
           near[1]["quartic_second_derivative_error_coefficient"])>2
print(json.dumps(dict(status="PASS",quartic_error_polynomial=str(S.factor(E0)),
    second_derivative_coefficient=str(S.factor(E2)),results=rows,
    authority="Original cubic stencil evaluated on quartic TEST polynomial; not a certified error bound or original F8 propagated solution"),indent=2))
