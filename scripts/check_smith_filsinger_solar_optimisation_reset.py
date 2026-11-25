"""Optimisation reset: exact passive ceiling, paid servo and causal C3 switching.
Donor equations transcribed from solar_paid_actuator (0626d752...) and
solar_phase_access (0542a681...). Normalized models, not physical admission.
"""
import json
import numpy as np
import sympy as s
from scipy.linalg import solve_banded
F,v,Rs,heat=s.symbols('F v Rs heat',real=True)
assert s.cancel(F*v-Rs*v*v-heat-(F*F/(4*Rs)-Rs*(v-F/(2*Rs))**2-heat))==0
# Original paid actuator: source RMS amplitude=1, Rs=RL=1, k=.25,
# y_peak=sqrt(1.5), g=1, m Omega^2=1. Same signed sideband solve.
def response(O,N,on,source):
    A=np.sqrt(1.5)*on; shift=A*A/2; n=np.arange(-N,N+1); freq=1+2*n*O
    diag=.25+shift-freq*freq+2j*freq
    ab=np.zeros((3,2*N+1),complex);ab[1]=diag;ab[0,1:]=shift/2;ab[2,:-1]=shift/2
    b=np.zeros(2*N+1,complex);b[N]=source/np.sqrt(2)
    x=solve_banded((1,1),ab,b);vel=1j*freq*x
    src=2*np.real(np.conj(b[N])*vel[N]);load=2*np.vdot(vel,vel).real
    exchange=2*load-src
    c=2*np.sum(x[1:]*np.conj(x[:-1]));exchange_direct=shift*O*c.imag
    assert abs(exchange-exchange_direct)<2e-9
    return src,load,exchange,O*shift
rows=[]
for O in (20,1000,2000,1560000):
    _,base,_,_=response(O,16,0,1)
    src,load,exchange,h=response(O,16,1,1)
    assert max(abs(a-b) for a,b in zip(response(O,8,1,1),(src,load,exchange,h)))<1e-10
    g=load-exchange;delta=g-base;ceiling=.25
    assert g<=ceiling+1e-13 and delta>0
    for Q in (100,10000,1000000,100000000):
        cost=h/Q
        assert g-cost<ceiling
        # Fixed servo trajectory: response scales linearly with source amplitude.
        for amp in (.5,2.,10.):
            assert np.allclose(response(O,16,1,amp)[:3],np.array([src,load,exchange])*amp**2,rtol=1e-8,atol=1e-10)
        rows.append(dict(Omega=O,Q=Q,detuned=base,optimal_static=ceiling,unit_active_before_friction=g,friction=cost,delta_vs_optimal=g-cost-ceiling,source_rms_break_even_absolute=float(np.sqrt(cost/g)),source_rms_break_even_detuned=float(np.sqrt(cost/delta)),source_rms_break_even_optimal=None))
# Exact C3 rank-one causal selection, general switching cost in units of
# incident block energy. Symmetric transition p on diagonal, r off diagonal.
p,c=s.symbols('p c',real=True);r=(1-p)/2;t=(p-s.Rational(1,3))/(1-p)
assert s.cancel(t-(p-r)/(1-p+r))==0
assert s.cancel(p-r-(1-p+r)*t)==0
assert s.cancel(p-(1-p)*t-s.Rational(1,3))==0
# Verify Bellman inequality and attaining action in every state. The
# two-valued bias depends on whether last observed state equals prior action.
checks=0
for pp in map(s.Rational,['1/3','1/2','3/4','9/10','99/100']):
    rr=(1-pp)/2;tt=(pp-s.Rational(1,3))/(1-pp)
    for cc in (s.Rational(0),tt/2,tt,tt+1,2*tt+1):
        gain=max(s.Rational(1,3),pp-(1-pp)*cc);h=min(cc,tt)
        for j in range(3):
            for k in range(3):
                scores=[]
                for a in range(3):
                    prob=pp if a==j else rr
                    scores.append(prob-cc*int(a!=k)+prob*h)
                assert max(scores)==gain+h*int(j==k)
                checks+=1
print(json.dumps(dict(status='CONDITIONAL_OPTIMISATION_RESET',servo=rows,bellman_states=checks,physical_admission=False),indent=2))
