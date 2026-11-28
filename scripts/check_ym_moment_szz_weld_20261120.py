"""Exact symbolic checks; not a physical source or Agda acceptance receipt."""
import sympy as s

N, u, target, rho, q, slack, defect = s.symbols('N u target rho q slack defect', positive=True)
K = lambda v: N/2-24*v/N-rho
assert s.simplify(K(u)-K(target)-24*(target-u)/N)==0
assert s.simplify(K(N**2/48-N*rho/24))==0
# Curvature subtraction: both source inequalities leave nonnegative slack.
assert s.expand((N/2-24*u/N)*q+slack-(rho*q-defect)-K(u)*q)==slack+defect
# Positive finite rational expectation, preserving the exact normalized weights.
w = [s.Rational(1,7),s.Rational(2,7),s.Rational(4,7)]
x = [s.Rational(-2,3),s.Rational(1,2),s.Rational(5,4)]
lam=s.Rational(1,3)
E=lambda f:sum(p*f(v) for p,v in zip(w,x))
assert E(lambda v:1)==1
for n in range(9):
    assert s.expand(E(lambda v:(lam*abs(v))**n)-lam**n*E(lambda v:abs(v)**n))==0
    # Positive Taylor partial sum bounds the nth term, exact rational.
    assert E(lambda v:sum((lam*abs(v))**j/s.factorial(j) for j in range(n+1))) >= lam**n*E(lambda v:abs(v)**n)/s.factorial(n)
# Counterexample to the old single-lambda denominator: deterministic X=20,
# lambda=1/10, n=2; exp(2)<9 by e<3, so RHS<180<400.
assert 20**2 > s.factorial(2)*9/s.Rational(1,10)
assert s.Rational(1,10)*20==2
# Window overlap is necessary, not provided by positivity of a target alone.
assert K(s.Rational(1,24)).subs({N:2,rho:s.Rational(1,4)})==s.Rational(1,4)
assert s.Rational(1,12)<1
print('PASS: SZZ margin difference, threshold, Hessian slack, finite normalized expectation, 9 factorial scalings, 9 Taylor bounds, old-bound counterexample, SU2 window fixture')
