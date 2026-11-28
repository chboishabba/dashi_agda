"""Exact finite-horizon passive comparator for a rational two-site receiving circuit.

All admissible scalar loads 0 <= q <= 2 are covered by a Sturm root count.
This is not a global passive optimum for the nonlinear atmospheric model.
"""
import json
import sympy as s


def run():
    q=s.symbols('q', real=True)
    h=s.Rational(1,2)
    amplitudes=[s.Integer(1),-s.Rational(1,2),s.Rational(1,3),s.Integer(0)]
    rotation=s.Matrix([[s.Rational(3,5),-s.Rational(4,5)],
                       [s.Rational(4,5),s.Rational(3,5)]])
    assert rotation.T*rotation==s.eye(2)
    x=s.zeros(2,1)
    useful=outgoing=incident=s.Integer(0)
    for a in amplitudes:
        midpoint=s.cancel((x[0]+h*a)/(1+h*(1+q)/2))
        next_local=s.Matrix([2*midpoint-x[0],x[1]])
        useful+=h*q*midpoint**2
        outgoing+=h*(midpoint-a)**2
        incident+=h*a*a
        x=rotation*next_local
    useful=s.factor(useful)
    outgoing=s.cancel(outgoing)
    storage=s.cancel(x.dot(x)/2)
    assert s.cancel(incident-outgoing-useful-storage)==0
    derivative=s.factor(s.diff(useful,q))
    numerator,denominator=s.fraction(derivative)
    assert s.count_roots(numerator,0,2)==0
    assert derivative.subs(q,1)>0
    # No stationary points and strictly positive derivative on the entire
    # feasible interval imply the unique global maximum at q=2.
    upper=s.cancel(useful.subs(q,2))
    assert upper>0 and upper<incident
    assert storage.subs(q,2)>0  # terminal state is not exactly restored
    # For an arbitrary active candidate A, A - upper is a rigorous lower
    # bound on its advantage for THIS scalar comparator only.
    return dict(status='EXACT_SCALAR_PASSIVE_GLOBAL_OPTIMUM',
        optimal_load='2',global_upper_J=str(upper),global_upper_float=float(upper),
        incident_J=str(incident),sturm_roots_in_interval=0,
        derivative_positive=True,energy_identity=True,original_restored=False,
        physical_admission=False)

if __name__=='__main__':
    print(json.dumps(run(),indent=2))
