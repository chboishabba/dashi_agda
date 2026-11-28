"""Original Dirichlet multi-base divisor selection, exact rational bounds.
No RH, native Bishop completion or kernel acceptance claim. The analytic
inequalities used here are derived in the four-P0 endpoint roadmap.
"""
from fractions import Fraction as Q
from math import factorial


def exact(x):
    if type(x) not in (int,Q):
        raise ValueError('exact rational required')
    return Q(x)


def ceil(x):
    return -(-x.numerator//x.denominator)


def add(a,b):
    return a[0]+b[0],a[1]+b[1]


def mul(a,b):
    return a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0]


def scale(t,a):
    return t*a[0],t*a[1]


def l1(a):
    return abs(a[0])+abs(a[1])


def log_unit_interval(x,J):
    # For 1<=x<=2, atanh series and exact geometric tail.
    x=exact(x)
    if not 1<=x<=2 or type(J) is not int or J<1:
        raise ValueError('invalid log series controls')
    t=(x-1)/(x+1)
    lo=2*sum((t**(2*j+1)/(2*j+1) for j in range(J)),Q(0))
    err=2*t**(2*J+1)/((2*J+1)*(1-t*t))
    return lo,lo+err


def log_nat_bounds(b,J):
    if type(b) is not int or b<1:
        raise ValueError('positive integer base required')
    k=b.bit_length()-1
    lo,hi=log_unit_interval(Q(b,2**k),J)
    a,c=log_unit_interval(Q(2),J)
    return lo+k*a,hi+k*c


def exp_enclosure(z,J):
    # Exact Gaussian rational polynomial with absolute l1 tail.
    if not isinstance(z,(tuple,list)) or len(z)!=2:
        raise ValueError('Gaussian rational pair required')
    z=tuple(exact(x) for x in z)
    r=l1(z)
    if type(J) is not int or J<1 or J+2<2*r:
        raise ValueError('insufficient Taylor degree for tail')
    p=t=(Q(1),Q(0))
    for j in range(1,J+1):
        t=scale(Q(1,j),mul(t,z))
        p=add(p,t)
    return p,2*r**(J+1)/factorial(J+1)


def divisor_enclosure(sigma,tau,b,J):
    sigma,tau=exact(sigma),exact(tau)
    lo,hi=log_nat_bounds(b,J)
    w=(1-sigma,-tau)
    center=scale((lo+hi)/2,w)
    perturb=l1(w)*(hi-lo)/2
    radius=l1(center)+perturb
    degree=max(J,ceil(2*radius))
    p,tail=exp_enclosure(center,degree)
    # |exp(z)-exp(z0)|_1 <= |z-z0|_1 exp(max(|z|_1,|z0|_1)).
    err=tail+perturb*3**ceil(radius)
    return (1-p[0],-p[1]),err


def adjacent_bases(sigma,tau):
    sigma,tau=exact(sigma),exact(tau)
    w=(1-sigma,-tau)
    if not l1(w):
        raise ValueError('s=1 is the actual pole, not a chart singularity')
    b=max(2,ceil(2*l1(w)))
    gap=max(abs(w[0]),abs(w[1]))/Q(8*(b+1))
    return b,b+1,gap


def choose_divisor(sigma,tau,max_terms=256):
    """Return a base and certified positive lower bound on |1-b^(1-s)|.

    The adjacent-chart lemma guarantees a nonzero denominator away from 1.
    Bounded computational resources are allowed to reject, never guess.
    """
    if type(max_terms) is not int or max_terms<4:
        raise ValueError('invalid term budget')
    a,b,gap=adjacent_bases(sigma,tau)
    J=4
    while J<=max_terms:
        for base in (a,b):
            # Cap the Taylor work as well as the log expansion.
            _,hi=log_nat_bounds(base,J)
            if ceil(2*l1((1-exact(sigma),-exact(tau)))*hi)>max_terms:
                continue
            p,err=divisor_enclosure(sigma,tau,base,J)
            lower=max(abs(p[0]),abs(p[1]))-err
            if lower>=gap/2:
                return base,lower
        J*=2
    raise ValueError('no divisor certified within term budget')


def tail_bound(base,delta,R,K):
    """All raw cutoffs N>=2^K; bound for periodic signed b-residual."""
    delta,R=exact(delta),exact(R)
    if type(base) is not int or base<2 or delta<=0 or R<delta or type(K) is not int or K<0:
        raise ValueError('invalid compact or cutoff')
    q=2/(2+delta)
    # Contractive subdivision gives variation <= (R/delta)
    # times the telescoping decrease in n^(-Re(s)).
    return (base-1)*(R/delta)*q**K


def cutoff_exponent(base,delta,R,eps,max_k=4096):
    eps=exact(eps)
    if eps<=0 or type(max_k) is not int or max_k<0:
        raise ValueError('invalid tolerance or budget')
    if tail_bound(base,delta,R,0)<=eps:
        return 0
    if tail_bound(base,delta,R,max_k)>eps:
        raise ValueError('cutoff exceeds budget')
    lo,hi=0,max_k
    while hi-lo>1:
        mid=(lo+hi)//2
        if tail_bound(base,delta,R,mid)<=eps:
            hi=mid
        else:
            lo=mid
    return hi
