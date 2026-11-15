#!/usr/bin/env python3
"""Exact ORIGINAL AdS5 a=t tensor family: H1 bulk energy does NOT bound Weyl.

On the original moving brane with THREE periodic brane spatial axes of
period 2pi, H_N=sin(N*x)cos(N*(T-Tstar))/N is independent of z and solves
L=-dTT+dzz-3/z dz+Delta3=0 exactly. Its actual Israel Neumann source is
n_in dH=b*v*H_T/sqrt(1-v²); neither the source nor domain is compact.
Weighted first-order energy is pi³/b(T)², independent of N; intrinsic 4D
electric Weyl magnitude at original t=2,Tstar,x=pi/(2N) is 9N/64.
This exact functional NO-GO means H1 energy and source L2 wall-flux
alone cannot control pointwise Weyl. It does NOT refute a compact FIO
existential early-arrival theorem or assert a measured graviton.
"""
import json,math
import sympy as sp
def symbolic():
    N=sp.symbols('N',integer=True,positive=True)
    T,z,x,Tstar,t=sp.symbols('T z x Tstar t',real=True,positive=True)
    h=sp.sin(N*x)*sp.cos(N*(T-Tstar))/N
    L=-sp.diff(h,T,2)+sp.diff(h,z,2)-3*sp.diff(h,z)/z+sp.diff(h,x,2)
    assert sp.simplify(L)==0
    HT=sp.diff(h,T);Hx=sp.diff(h,x)
    S=sp.sqrt(1+t*t)/t
    Hetaeta=S*S*sp.diff(h,T,2)-HT/(t*sp.sqrt(1+t*t))
    E4=-(Hetaeta+sp.diff(h,x,2))/(4*t*t)
    peak=sp.simplify(E4.subs({t:2,T:Tstar,x:sp.pi/(2*N)}))
    assert sp.simplify(peak-sp.Rational(9,64)*N)==0
    v,b=sp.symbols('v b',real=True)
    G=b*v*HT/sp.sqrt(1-v*v)
    assert sp.simplify(G.subs(T,Tstar))==0
    assert G!=0
    xint=sp.integrate(HT**2+Hx**2,(x,0,2*sp.pi))
    assert sp.simplify(xint-sp.pi)==0
    energy=sp.simplify(sp.Rational(1,2)*xint*(2*sp.pi)**2/(2*b*b))
    assert sp.simplify(energy-sp.pi**3/b**2)==0
    return dict(exact_bulk_wave_residual='0',
       mode='sin(N*x)cos(N*(T-Tstar))/N',
       original_Israel_G='b*v*H_T/sqrt(1-v²)',
       periodic_3torus_not_compact_R3=True,
       original_bulk_weighted_first_order_energy='pi³/b(T)² independent of N',
       original_t2_E4_peak='9*N/64',
       H1_to_pointwise_Weyl_bounded=False,
       compact_source_FIO_theorem_refuted=False)
def audit():
    a=symbolic()
    rows=[dict(N=n,weighted_H1_energy=4*math.pi**3,
        intrinsic_4D_Weyl_at_t2=9*n/64) for n in (4,8,16,32,64,128)]
    assert len({r['weighted_H1_energy'] for r in rows})==1
    assert rows[-1]['intrinsic_4D_Weyl_at_t2']==2*rows[-2]['intrinsic_4D_Weyl_at_t2']
    return dict(symbolic=a,samples=rows,
       source_to_receiver_higher_Sobolev_trace_bound_needed=True,
       same_original_a_equals_t_model=True,
       experimental_graviton_observed=False)
if __name__=='__main__':print(json.dumps(audit(),indent=2))
