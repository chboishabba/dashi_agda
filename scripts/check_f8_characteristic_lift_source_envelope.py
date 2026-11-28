"""Original F8 finite-band source-driven characteristic E0 rational certificate.

Given a smooth original lifted R/L/H solution on 1<=t<=6/5,
homogeneous initial data and q=12 Pi, the previous energy inequality
implies E(t)<=exp(81/5)/20 * [(199+50K²)(12P0)²+2(12P1)²],
where P0,P1 are original prescribed source C1 envelopes.
exp(81/5) is bounded by an exact rational Taylor tail, not by float.
No continuum discretization or full coupled Einstein certification.
"""
from fractions import Fraction as F
from math import factorial


def exp_upper(x,degree=100):
    x=F(x)
    if x<0 or degree<1 or x>=degree+2:
        raise ValueError('Taylor tail ratio must be <1')
    total=sum(x**j/factorial(j) for j in range(degree+1))
    next_term=x**(degree+1)/factorial(degree+1)
    return total+next_term/(1-x/F(degree+2))


def energy_upper(K,P0,P1):
    K,P0,P1=map(F,(K,P0,P1))
    if min(K,P0,P1)<0:
        raise ValueError('nonnegative cutoff and source caps')
    forcing=(199+50*K*K)*(12*P0)**2+2*(12*P1)**2
    return exp_upper(F(81,5))*forcing/20


def exact():
    from check_f8_original_pulse_derivative_bounds import fourier_source_bounds
    K=F(40)
    P=fourier_source_bounds(K,1)
    bound=energy_upper(K,*P)
    assert bound>0
    assert energy_upper(0,0,0)==0
    assert energy_upper(K,2*P[0],2*P[1])==4*bound
    assert energy_upper(K,P[0],2*P[1])>bound
    assert exp_upper(F(81,5))>0
    print('PASS original F8 finite-band source-driven E0 rational envelope, K=40')
    print('Energy cap upper decimal:',format(float(bound),'.6e'))
    print('No high-time continuum or numerical stability certification')

if __name__=='__main__':exact()
