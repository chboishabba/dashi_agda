"""F8 XCVIII: original moving-wall Israel/kinematic trace compatibility.

Exact SymPy on the original (U,P,M) characteristic definitions, original
v=-1/sqrt(1+t^2), prescribed Israel flux A, and physical p=U_T-vU_y.
Uses action-derived (W,q) variables for an invertible field/flux map.
Does not change the native solver or pretend the boundary trace evolves
automatically, nor claim source-to-curvature or continuum convergence.
No CI.
"""
import json
import sympy as s

t=s.symbols('t',positive=True)
v,A,W=s.symbols('v A W',real=True)
Ad,Wd,vd,DW=s.symbols('A_t W_t v_t D_y_W',real=True)
a,c=1+v,1-v
d=a*c
P=(W+A)/a
M=(W-A)/c
qstar=s.factor((P-M)/2)
assert s.factor(qstar-(A-v*W)/d)==0
assert s.simplify((a*P+c*M)/2-W)==0
assert s.simplify((a*P-c*M)/2-A)==0
assert s.simplify((P-M)/2-qstar)==0
assert s.factor(s.det(s.Matrix([[a/2,c/2],[a/2,-c/2]]))+d/2)==0

vphys=-1/s.sqrt(1+t*t)
assert s.simplify(1-vphys**2-t*t/(1+t*t))==0
assert s.simplify(s.diff(vphys,t)-t/(1+t*t)**s.Rational(3,2))==0
Fprime=s.sqrt(1+t*t)/t**2
vT=s.simplify(s.diff(vphys,t)/Fprime)
assert s.simplify(vT-t**3/(1+t*t)**2)==0

qt=s.factor(s.diff(qstar,A)*Ad+s.diff(qstar,W)*Wd+s.diff(qstar,v)*vd)
assert s.simplify(qt-((Ad-vd*W-v*Wd)/d+2*v*vd*(A-v*W)/d**2))==0
trace_rate=s.factor(qt-DW)
assert trace_rate!=0
assert s.simplify(trace_rate.subs({Ad:0,Wd:0,vd:0,DW:0}))==0
neg=s.factor(trace_rate.subs({v:-s.Rational(3,5),A:1,W:0,Ad:0,
                              Wd:0,vd:s.Rational(1,4),DW:0}))
assert neg==-s.Rational(375,512)

p=s.factor(W-v*qstar)
work=s.factor(p*qstar+v*(p*p+qstar*qstar)/2)
assert s.simplify(work-(2*A*W-v*(A*A+W*W))/(2*d))==0
assert s.limit(P.subs(v,vphys),t,s.oo)==W+A
assert s.limit(M.subs(v,vphys),t,s.oo)==W-A
for ts in (s.Integer(1),s.Integer(12)):
    z=vphys.subs(t,ts)
    assert s.N(1/(1-z*z))<=2
    assert s.N(1/(1+z))<=s.N(2+s.sqrt(2))
print(json.dumps(dict(status="PASS",
    characteristic_P=str(s.factor(P)),characteristic_M=str(s.factor(M)),
    geometry_trace_q=str(qstar),time_derivative_q=str(qt),
    unpaid_trace_evolution=str(trace_rate),
    moving_negative_control=str(neg),normal_flux_work=str(work),
    original_v_T=str(vT),physical_boundary_map_determinant=str(-d/2),
    limitation="Exact compatible variable map and moving trace obligation only; not full SSPRK3 preservation, forced boundary energy estimate, production repair or physical far-null"),indent=2))
