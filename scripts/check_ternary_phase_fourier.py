"""Complex four-point phase transfer and ideal temporal-slit negative controls.

Reconstructs periodic midpoint receiver/source response from independent
nonlinear forward solutions; not measured optical or environmental response.
"""
import numpy as np
import sympy as sp
from check_ternary_periodic_norton import fixture, PERIOD
from check_ternary_stationary_cycle import incidence


def exact_fourier():
    x0,x1,x2,x3=sp.symbols('x0 x1 x2 x3',real=True)
    x=[x0,x1,x2,x3]
    c1=sum(x[k]*sp.I**(-k) for k in range(4))/4
    assert sp.expand(c1-(x0-sp.I*x1-x2+sp.I*x3)/4)==0
    assert sp.expand(c1-sp.conjugate(sum(x[k]*sp.I**k for k in range(4))/4))==0
    # Rectangular temporal aperture: exact finite-width interference
    w,T,tau=sp.symbols('w T tau',real=True,nonzero=True)
    single=2*sp.sin(w*T/2)/w
    pair=single*(1+sp.exp(-sp.I*w*tau))
    intensity=sp.expand_complex(pair*sp.conjugate(pair))
    assert sp.trigsimp(sp.expand(intensity-single**2*(2+2*sp.cos(w*tau))))==0
    assert sp.limit(single,w,0)==T
    assert sp.simplify(pair.subs(tau,0)-2*single)==0
    return 5


def fundamental(x):
    return np.fft.fft(np.asarray(x,dtype=float))[1]/len(x)


def optical_slit(tau,T=1.,omega=.8):
    envelope=2*np.sin(omega*T/2)/omega
    return envelope*(1+np.exp(-1j*omega*tau))


def run():
    checks=exact_fourier()
    for dim in (2,3):
        for beta in (0.,.45):
            # A physical periodic response and its DC control from the SAME solver.
            active=fixture(dim,beta,.12,return_states=True)
            dc=fixture(dim,beta,0.,return_states=True)
            states=active['states']; n=3**dim; ne=incidence(dim).shape[1]
            mid=(states+np.roll(states,-1,axis=0))/2
            source=mid[:,0]; receiver=mid[:,1]; far_receiver=mid[:,n-1]
            polarized=mid[:,n+ne]
            driving=.3+.12*np.array([0,1,0,-1],float)
            source_ac=fundamental(driving)
            receiver_ac=fundamental(receiver)
            source_field_ac=fundamental(source)
            P_ac=fundamental(polarized)
            ratio=receiver_ac/source_ac
            assert abs(source_ac)>1e-3; checks+=1
            assert abs(receiver_ac)>1e-7 and abs(P_ac)>1e-7;checks+=1
            assert abs(fundamental(far_receiver))<1e-9;checks+=1
            assert abs(fundamental(dc['states'][:,1]))<1e-10;checks+=1
            # phase is complex; power-only observation removes it.
            assert abs(abs(receiver_ac)**2-abs(receiver_ac*np.exp(1j*.7))**2)<1e-14; checks+=1
            # Reconstruct receiver's four midpoints from all four harmonics.
            assert np.max(abs(np.fft.ifft(np.fft.fft(receiver))-receiver))<1e-12;checks+=1
            assert active['residual']<1e-10 and abs(active['storage_change'])<1e-10;checks+=1
            print(f'{dim}D beta={beta}: near-site H1={ratio.real:.9g}{ratio.imag:+.9g}j, phase={np.angle(ratio):+.6f}, |near1|={abs(receiver_ac):.7g}, |far1|={abs(fundamental(far_receiver)):.3g}, |Psrc1|={abs(P_ac):.7g}')
    # Explicit phase response of finite-width optical slit: no supplied data.
    for tau in (0.,1.0,2.0):
        measured=abs(optical_slit(tau))**2
        predicted=(2*np.sin(.8/2)/.8)**2*(2+2*np.cos(.8*tau))
        assert abs(measured-predicted)<1e-12;checks+=1
    assert abs(optical_slit(0))>abs(optical_slit(2));checks+=1
    print(f'{checks}/{checks} PASS: phase-sensitive periodic response + ideal finite-width slit, SymPy {sp.__version__}')


if __name__=='__main__':run()
