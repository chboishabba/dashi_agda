"""Exact Bernstein global bounds for two passive loads on a finite signed circuit.

All nonnegative lambda1 + lambda2 <= 2 are parametrized by
lambda1=2*u, lambda2=2*(1-u)*v with (u,v) in [0,1]^2.
This is a finite reference circuit, not a physical atmospheric admission.
"""
from itertools import product
from math import comb
import json
import sympy as s

u,v=s.symbols('u v', real=True)

def bernstein_range(expr):
    poly=s.Poly(s.expand(expr),u,v)
    n,m=poly.degree_list(); terms=dict(poly.terms())
    coeff=[]
    for i in range(n+1):
        for j in range(m+1):
            b=sum((c*s.Rational(comb(i,a),comb(n,a))*s.Rational(comb(j,b),comb(m,b))
                   for (a,b),c in terms.items() if a<=i and b<=j),s.Integer(0))
            coeff.append(b)
    return min(coeff),max(coeff)

def circuit():
    h=s.Rational(1,3);load1=2*u;load2=2*(1-u)*v
    x=y=s.Integer(0);work=reflected=incident=s.Integer(0)
    for a in (s.Integer(1),-s.Rational(1,2),s.Integer(0)):
        m1=s.cancel((x+h*a)/(1+h*(1+load1)/2))
        after1=s.cancel(2*m1-x)
        m2=s.cancel(y/(1+h*load2/2))
        after2=s.cancel(2*m2-y)
        work+=h*(load1*m1**2+load2*m2**2)
        reflected+=h*(m1-a)**2
        incident+=h*a*a
        x,y=s.cancel((3*after1-4*after2)/5),s.cancel((4*after1+3*after2)/5)
    return s.factor(work),s.factor(x),s.factor(y),s.cancel(incident-reflected-(x*x+y*y)/2-work),incident

def run(grid=8):
    work,x,y,energy_error,incident=circuit()
    assert energy_error==0
    xn,xd=s.fraction(x)
    xlo,xhi=bernstein_range(xn);dlo,dhi=bernstein_range(xd)
    assert xhi<0 and dlo>0 # strictly negative terminal x for every admissible load
    pn,pd=s.fraction(work)
    low,high=bernstein_range(pn); qlow,qhigh=bernstein_range(pd)
    assert low>=0 and qlow>0
    # Every box is covered. Bernstein polynomial convex-hull bounds are exact
    # inequalities over each box; ratios are enclosed since denominator > 0.
    upper=s.Integer(0)
    for i,j in product(range(grid),repeat=2):
        z={u:s.Rational(i,grid)+u/s.Integer(grid),v:s.Rational(j,grid)+v/s.Integer(grid)}
        pmax=bernstein_range(pn.subs(z,simultaneous=True))[1]
        qmin=bernstein_range(pd.subs(z,simultaneous=True))[0]
        assert qmin>0
        upper=max(upper,pmax/qmin)
    witness=work.subs({u:s.Rational(1,2),v:s.Rational(1,2)})
    assert 0<witness<=upper<incident
    return dict(status='PASS',subboxes=grid**2,free_load_dimension=2,
        global_return_obstructed=True,terminal_x_numerator_bernstein_upper=str(xhi),
        denominator_bernstein_lower=str(dlo),
        passive_upper_exact=str(upper),passive_upper_float=float(upper),
        interior_witness_exact=str(witness),incident_J=str(incident),
        energy_identity=True,physical_admission=False,
        scope='finite circuit; global bound includes UNRESTORED allocations')

if __name__=='__main__':
    print(json.dumps(run(),indent=2))
