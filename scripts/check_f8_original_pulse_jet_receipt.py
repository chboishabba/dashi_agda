"""F8 prescribed compact source: literal donor bump/coefficient numerical replay.

High-precision independent clock differentiation cross-checks the local
five-point source jets. Certified errors come ONLY from independent global
C5/C6 bounds, never from the numerical h/2 difference.
"""
import numpy as np
import mpmath as mp
from check_f8_characteristic_history import bump, coefficient
from check_f8_original_pulse_derivative_bounds import fourier_source_bounds
from check_f8_ward_timejet_receipt import jets
from check_f8_timejet_stencil_certificate import certified


def original_mp(t):
    F=lambda z:mp.asinh(z)-mp.sqrt(1+z*z)/z
    x=2*(F(t)-F(mp.mpf(1)))/mp.mpf('0.065')-1
    return mp.exp(1-1/(1-x*x)) if abs(x)<1 else mp.mpf(0)


def exact_sample(t0=1.035,h=.001,cutoff=40.):
    mp.mp.dps=80
    k=np.array([0.,5.,20.,cutoff])
    c=coefficient(k)
    # Check the scalar factor in exactly the stored original source owner.
    for t in (1.,1.005,1.02,1.035,1.06,1.2):
        assert abs(bump(t)-float(original_mp(mp.mpf(str(t)))))<5e-14
    maxc=(4*np.pi/3)*(.04**7)*cutoff**4
    assert np.max(abs(c))<=maxc*(1+1e-12)
    assert c[0]==0
    # Signed complex modes: the source is real even in k, and zero mode is zero.
    shape=np.diag([0.,1.,-1.]).astype(complex)
    calc=lambda t:tuple(ci*bump(t)*shape for ci in c)
    result=jets(calc,t0,h)
    caps=fourier_source_bounds(cutoff,6)
    cert=certified(h,float(caps[5]),float(caps[6]))
    oracle=[]
    for j in (1,2):
        scalar=mp.diff(original_mp,mp.mpf(str(t0)),j)
        oracle.append(tuple(float(ci*float(scalar))*shape for ci in c))
    d1=max(np.max(abs(x-y)) for x,y in zip(result['dt'],oracle[0]))
    d2=max(np.max(abs(x-y)) for x,y in zip(result['dtt'],oracle[1]))
    assert d1<=cert['dt'] and d2<=cert['dtt']
    # Independent pointwise accuracy is diagnostic; bound is valid only
    # because of the analytic source derivative certificate.
    assert d1<1e-6 and d2<1e-3
    print('PASS original F8 bump/coefficient/pi Fourier time-jets', 'K',cutoff)
    print('diagnostic errors dt,dtt:',d1,d2)
    print('certified prescribed-Pi allowances dt,dtt:',cert)
    print('H and retarded A2 certificates remain OPEN')

if __name__=='__main__':exact_sample()
