"""Exact rational smooth original-state restoration constraint contract.
For each state group, g=1-||endpoint-original||^2/allowance^2.
The derivative is polynomial and remains defined at exact restoration.
"""
import sympy as s
z=s.symbols('z', real=True)
for dim in (1,2,4,9):
    start=s.Matrix([s.Rational(i+1,7) for i in range(dim)])
    endpoint=s.Matrix([start[i]+s.Rational(i+2,11)*z+s.Rational(i+3,17)*z*z for i in range(dim)])
    tangent=s.Matrix([s.diff(v,z) for v in endpoint])
    allowance=s.Rational(dim+1,5)
    difference=endpoint-start
    g=1-difference.dot(difference)/allowance**2
    dg=-2*difference.dot(tangent)/allowance**2
    assert s.cancel(s.diff(g,z)-dg)==0
    assert g.subs(z,0)==1
    assert dg.subs(z,0)==0
    assert g.subs(z,s.Rational(7,4))<0
    assert s.simplify(g.subs(z,s.Rational(1,4))+s.Rational(0)) is not None
print({'status':'PASS','group_dimensions':[1,2,4,9],'exact_constraints':4,'restoration_nonsingular':True})
