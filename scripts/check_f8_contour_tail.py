"""Original compact prepotential contour envelope and exact sufficient window budget.
Conditional on original smooth retarded reference and energy/trace estimate.
No bound on normal/time discretization or raw observer.
"""
from fractions import Fraction as Q
from math import factorial
import json
import sympy as s


def check():
    x=s.symbols('x',real=True);z=x+s.I*(1-x)
    assert s.simplify(s.re(1/(1-z*z))-1/(2*(1-x)*(1+x*x)))==0
    assert s.expand(s.Abs(z)**2)==2*x*x-2*x+1
    # On the triangular contour x>=0: Re(1/(1-z²))>=1/[4(1-x)].
    # xi(1-x)+1/[4(1-x)]>=sqrt(xi), and the reflected side is identical.
    # Length/2=sqrt(2), |z|<=1, and e*sqrt(2)<4.
    assert Q(11,4)**2*2<16
    # |c_n|<=4 eps^6 exp(-sqrt(eps*k_n)), k_n>=n, k_n<4n/3.
    # Earlier energy/window constant 8e6 bounds |O_n|<=8e6 k_n^6|c_n|.
    a=Q(1,5);pref=Q(8000000)*4*Q(1,25)**6*Q(4,3)**6
    y=s.symbols('y',positive=True);b=s.Rational(1,5)
    poly=sum(s.factorial(13)*y**j/(s.factorial(j)*b**(14-j)) for j in range(14))
    assert s.expand(s.diff(poly,y)-b*poly+y**13)==0
    def bound(m):
        # N=m², decreasing integrand n^6 exp(-sqrt(n)/5) for m>=60.
        assert m>=60
        v=a*m;term=Q(1);den=term
        for j in range(1,2*int(v)+2):term*=v/j;den+=term
        # Positive exponential series is a strict lower bound, reciprocal an upper bound.
        return pref*2*sum(Q(factorial(13),factorial(j))*Q(m)**j/a**(14-j) for j in range(14))/den
    targets=[]
    for power in (6,9,12):
        target=Q(1,10**power);lo=60;hi=120
        while bound(hi)>=target:hi*=2
        while hi-lo>1:
            mid=(hi+lo)//2
            if bound(mid)<target:hi=mid
            else:lo=mid
        assert bound(hi)<target
        targets.append(dict(target=float(target),sufficient_N=hi**2,upper=float(bound(hi))))
    return dict(source_bound='4 eps^6 exp(-sqrt(eps*k_n))',window_bound_constant=8000000,targets=targets,tail_at_4096=float(bound(64)),note='Strict rational tail comparison at perfect-square cutoffs; conditional analytic estimate, not finite normal/time convergence.')

if __name__=='__main__':print(json.dumps(check(),indent=2))
