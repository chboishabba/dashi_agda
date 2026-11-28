"""Natural ionisation observation and constitutive identities; no actuation model."""
import json
import sympy as s
n,m,nu=s.symbols('n m nu',positive=True)
q,B=s.symbols('q B',real=True)
J=s.Matrix([[0,-1],[1,0]])
I=s.eye(2)
# Steady neutral-frame drift: m nu v = q(E + v cross B).
A=m*nu*I+q*B*J
S=n*q*q*A.inv()
P=n*q*q*m*nu/((m*nu)**2+(q*B)**2)
H=-n*q**3*B/((m*nu)**2+(q*B)**2)
assert (S-P*I-H*J).applyfunc(s.simplify)==s.zeros(2)
assert ((S+S.T)/2-P*I).applyfunc(s.simplify)==s.zeros(2)
assert s.simplify(s.diff(P,n)-P/n)==0
# The density response is conditional on fixed collision and magnetic state.
assert P.subs({m:1,q:1,B:1,n:1,nu:1})!=P.subs({m:1,q:1,B:1,n:1,nu:2})
# Local energy transfer: separate paid energy, chemical storage, and other loss.
N,C,R,F,e,w=s.symbols('N C R F e w',nonnegative=True)
# N/C = natural/other creation rate; R = removal; F = outward pair flux.
ndot=N+C-R-F
assert s.expand(w*(N+C)-(e*ndot+e*R+e*F+(w-e)*(N+C)))==0
# EISCAT's Qp proxy is proportional to n^2 at fixed alpha and pair cost.
# Two equal-weight positive-density cells have identical integrated proxy,
# different conductance, even with fixed equal mobility coefficients.
a=s.Matrix([5,5]);b=s.Matrix([1,7]);k=s.ones(2,1)
assert a.dot(a)==b.dot(b)==50 and k.dot(a)==10 and k.dot(b)==8
# Density and proxy can coincide while independent collision physics differs.
# Pointwise pair-production proxy equals actual creation only at local balance.
alpha=s.symbols('alpha',positive=True)
assert s.expand((N+C-alpha*n*n-F)-(N+C-R-F)).subs(R,alpha*n*n)==0
# Reuse common-source observation principle: no inference of ground work.
print(json.dumps(dict(status='CONDITIONAL_IONISATION_CONSTITUTIVE_IDENTITIES',sympy=s.__version__,checks=6,proxy_collision=dict(sum_density_squared=50,conductance_coordinates=[10,8]),physical_admission=False,scope='Stationary fixed-species drift, simplified pair ledger, abstract density profiles; no calibrated atmosphere or control design'),indent=2))
