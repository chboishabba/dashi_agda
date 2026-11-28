"""F8 XCIX: existing H=z^4 original AdS5 moving-wall manufactured witness.

Separates continuum zero kinematic constraint from the original one-sided
finite-difference boundary trace truncation and its physical T derivative.
Source is manufactured nonhomogeneous Israel, NOT original compact TT pulse.
No CI, full production replay, physical acceptance or new PDE.
"""
import json
import sympy as s

z,y=s.symbols("z y",positive=True)
t=s.symbols("t",positive=True)
b=1/t;v=-1/s.sqrt(1+t*t);vT=t**3/(1+t*t)**2
H=z**4
assert s.simplify(s.diff(H,z,2)-3*s.diff(H,z)/z)==0
U=(b+y)**4
q=s.diff(U,y)
W=q*v
P=s.factor(W+(1-v)*q)
M=s.factor(W-(1+v)*q)
assert s.simplify(P-4*(b+y)**3)==0
assert s.simplify(M+4*(b+y)**3)==0
A=s.factor((1+v)*P/2-(1-v)*M/2)
assert s.simplify(A-4*(b+y)**3)==0
assert s.simplify((P-M)/2-q)==0
Fprime=s.sqrt(1+t*t)/t**2
def ddt(f):return s.simplify(s.diff(f,t)/Fprime)
assert s.simplify(ddt(b)-v)==0
assert s.simplify(ddt(q)-s.diff(W,y))==0
assert s.simplify(ddt(v)-vT)==0
assert s.factor(W-v*q)==0

h=s.symbols("h",positive=True)
qdisc=s.factor((U.subs(y,h)-U.subs(y,0))/h)
qtrue=s.factor(q.subs(y,0))
Q=s.factor(qtrue-qdisc)
assert s.expand(Q+6*b*b*h+4*b*h*h+h**3)==0
Qdot=s.factor(ddt(Q))
assert s.simplify(Qdot+12*b*v*h+4*v*h*h)==0
assert s.simplify(2*(A.subs(y,0)-(
 (1+v)*P.subs(y,0)-(1-v)*M.subs(y,0))/2)/h)==0
slice=s.Rational(4,3)
rows=[]
for hh in (s.Rational(1,10),s.Rational(1,20),s.Rational(1,40)):
    rows.append(dict(h=str(hh),flux=str(s.simplify(A.subs({y:0,t:slice}))),
                     W=str(s.simplify(W.subs({y:0,t:slice}))),
                     Q_h=str(s.simplify(Q.subs({h:hh,t:slice}))),
                     Q_h_T=str(s.simplify(Qdot.subs({h:hh,t:slice}))),
                     native_mode3_wall_Qdot_on_exact_flux="0"))
assert [r["Q_h"] for r in rows]==["-737/2000","-1411/8000","-5521/64000"]
assert [r["Q_h_T"] for r in rows]==["141/250","69/250","273/2000"]
print(json.dumps(dict(status="PASS",continuum_Q="0",manufactured_H="z^4",
 original_discrete_Q=str(Q),moving_trace_Q_T=str(Qdot),
 rational_slice=str(slice),rows=rows,
 limitation="Manufactured moving wall trace error scales O(h); not a full discrete solution, compact TT source, energy stability, or a far causal-null repair."),indent=2))
