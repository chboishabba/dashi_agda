#!/usr/bin/env python3
"""ORIGINAL moving a=t AdS5 Israel Neumann forced characteristic energy.

qminus=beta qplus - 2G/(1-v), beta=(1+v)/(1-v), v=-1/sqrt(1+t²).
Incoming minus outgoing characteristic flux exactly:
F=(1-v)||qminus||²-(1+v)||qplus||²
 = 2v beta ||qplus-G/v||² - 2||G||²/v <= 2sqrt(1+t²)||G||²
 <= 2sqrt5 ||G||² on original t in [1,2].
This is a true componentwise wall flux bound, NOT a full SSPRK3 energy,
physical source action or an early curvature detection theorem.
"""
import math,json
import sympy as sp
import numpy as np

def symbolic():
    v,q,g=sp.symbols('v q g',real=True,nonzero=True)
    beta=(1+v)/(1-v)
    m=beta*q-2*g/(1-v)
    flux=(1-v)*m*m-(1+v)*q*q
    square=2*v*beta*(q-g/v)**2-2*g*g/v
    assert sp.factor(flux-square)==0
    slice43=-sp.Rational(3,10)*(q+sp.Rational(5,3)*g)**2+sp.Rational(10,3)*g*g
    assert sp.factor(flux.subs(v,-sp.Rational(3,5))-slice43)==0
    return dict(exact_forced_boundary_square=True,
        general_identity='F=2v*beta*||qplus-G/v||²-(2/v)*||G||²',
        original_t43_identity='F=-3/10*(qplus+5G/3)²+10G²/3')

def evaluate(t,qplus,G):
    if not 1<=t<=2:raise ValueError('original t interval [1,2]')
    v=-1/math.sqrt(1+t*t);beta=(1+v)/(1-v)
    p=np.asarray(qplus,dtype=float);g=np.asarray(G,dtype=float)
    if p.shape!=g.shape:raise ValueError('matching TT source/polarization components')
    m=beta*p-2*g/(1-v)
    flux=float((1-v)*np.sum(m*m)-(1+v)*np.sum(p*p))
    square=float(2*v*beta*np.sum((p-g/v)**2)-(2/v)*np.sum(g*g))
    upper=float(-2/v*np.sum(g*g))
    assert math.isclose(flux,square,rel_tol=1e-11,abs_tol=1e-11)
    assert flux<=upper+1e-11
    return dict(t=t,beta=beta,wall_v=v,
        actual_incoming_minus_outgoing_characteristic_flux=flux,
        exact_square_flux=square,uniform_forced_bound=upper,
        bound_constant=-2/v,
        homogeneous_dissipative=bool(np.sum(g*g)==0 and flux<=1e-12),
        physical_receiver_Weyl_convergence=False)

def audit():
    rows=[evaluate(t,[1/8,2/7],[1/12,-1/17])
          for t in (1.,4/3,2.)]
    assert all(r['bound_constant']<=2*math.sqrt(5)+1e-12 for r in rows)
    return dict(symbolic=symbolic(),rows=rows,
        uniform_original_t_1_2_constant='2 sqrt(5)',
        original_forced_wall_flux_bound_closed=True,
        full_time_discrete_CFL_and_receiver_trace_open=True,
        physical_observation=False)
if __name__=='__main__':print(json.dumps(audit(),indent=2))
