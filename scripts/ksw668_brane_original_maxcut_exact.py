#!/usr/bin/env python3
"""PR #1504 exact/local brane max-cut A3/A4/B2/B3/B5, mathematical checks only.

Original sources: Caldwell–Langlois (2001), Maartens–Koyama (2010).
Static double-disc cylinder is a NEW model, not the original AdS5 FRW.
No physical retarded TT Green function, experimental receiver or Agda receipt.
"""
import json, math
import sympy as s

def gauss5():
    p=math.sqrt(5-2*math.sqrt(10/7))/3
    q=math.sqrt(5+2*math.sqrt(10/7))/3
    wp=(322+13*math.sqrt(70))/900
    wq=(322-13*math.sqrt(70))/900
    return [(-q,wq),(-p,wp),(0.,128/225),(p,wp),(q,wq)]

def early_thin_receiver(delta=.02,t=2.125,tau=.25):
    """Codimension-one q(t) f(theta,u,v) delta(r-1) in 4-spatial bulk."""
    low=2*math.cos(delta/2)
    high=math.sqrt(4+2*delta*delta)
    assert 0<delta<.1 and t-tau<low<high<t<math.pi
    prof=lambda a:15/16*(1-a*a)**2
    # Correct FIVE-dimensional retarded ramp kernel, not 3D Huygens delta.
    ret=lambda time,d: math.sqrt(time*time-d*d)/(4*math.pi**2*d*d) if time>d else 0.
    response=0.
    for a,wa in gauss5():
      for b,wb in gauss5():
       for c,wc in gauss5():
        d=math.sqrt(2+2*math.cos(delta*a)+delta*delta*(b*b+c*c))
        response+=wa*wb*wc*prof(a)*prof(b)*prof(c)*(ret(t,d)-2*ret(t-tau,d)+ret(t-2*tau,d))
    lo,hi=ret(t,high),ret(t,low)
    assert 0<lo<response<hi and response<.01
    # F=f_delta delta_Sigma in Hdot^-1(R4) by smooth compact trace and
    # low-frequency integrability. q in W1,1 with q(0)=0.
    # Duhamel + integration by parts in time yields
    # sqrt(2E)<= (|q(t)|+int_0^t |q'|) ||F||_Hdot^-1
    # <=3*tau*||F||_Hdot^-1 ; E<=9/2*tau²||F||².
    return dict(status='PASS',source='compact thin-brane sheet distribution in flat 5D test bulk',
                finite_energy_by_Hdot_minus1_time_IBP=True,
                energy_bound_factor_Hdot_minus1_squared=4.5*tau*tau,
                receiver_time=t,photon_time=math.pi,
                positive_lower=lo,receiver=response,positive_upper=hi,
                self_gravitating_metric_used=False)

def static_z2_winding():
    """Glue two flat interior discs 0<=r<=R, inward normals Kθθ=-1/R."""
    R,k,T,f,n=s.symbols('R k T f n',positive=True)
    K=s.diag(0,-1/R,0,0)
    rhs=(-2/k*(K-s.trace(K)*s.eye(4))).applyfunc(s.simplify)
    az=f*f*n*n/(2*R*R)
    src=s.diag(-T-az,-T+az,-T-az,-T-az)
    assert rhs==s.diag(-2/(k*R),0,-2/(k*R),-2/(k*R))
    assert src.subs({R:1,T:2,f:2,n:1})==rhs.subs({R:1,k:s.Rational(1,2)})
    energy=2*s.pi*T*R+s.pi*f*f*n*n/R
    assert s.diff(energy,R).subs({T:2,f:2,n:1,R:1})==0
    assert s.simplify(s.diff(energy,R,2).subs({T:2,f:2,n:1,R:1})-8*s.pi)==0
    aa=s.symbols('aa')
    matter=s.diag(-T-aa,-T+aa,-T-aa,-T-aa)
    assert (matter-rhs).subs({T:1/(k*R),aa:1/(k*R)})==s.zeros(4)
    return dict(status='PASS static full Z2 Israel + winding stress',
                source_stress_mixed=str(src),israel_stress_mixed=str(rhs),
                tuning='T=f² n²/(2R²)=1/(kappa5² R)',
                example='R=1 T=2 f=2 n=1 kappa5²=1/2',
                radial_probe_stiffness='8*pi',coupled_stability=False)

def linear_TT_israel():
    """Mixed-index dimensionless H; cancellation of background K*H."""
    ep,a,ks,kappa=s.symbols('ep a ks kappa',real=True)
    hp,hx,gp,gx,pp,px=s.symbols('hp hx gp gx pp px',real=True)
    H=s.Matrix([[0,0,0],[0,hp,hx],[0,hx,-hp]])
    Hn=s.Matrix([[0,0,0],[0,gp,gx],[0,gx,-gp]])
    pi=s.Matrix([[0,0,0],[0,pp,px],[0,px,-pp]])
    qinv=(s.eye(3)-ep*H)/a**2
    Kcov=a**2*(ks*(s.eye(3)+ep*H)+ep*Hn/2)
    deltaK=(qinv*Kcov).applyfunc(lambda e:s.expand(e).coeff(ep,1))
    assert deltaK==Hn/2
    assert (deltaK+kappa*pi/2).subs({gp:-kappa*pp,gx:-kappa*px})==s.zeros(3)
    t=s.symbols('t',positive=True)
    vel=-1/s.sqrt(1+t*t)
    assert -1<vel.subs(t,1)<0
    return dict(status='PASS two-polarization linearized mixed-index Israel',
                dimensionless_TT_boundary='n^A partial_A H_i^j=-kappa5²*pi_i^j',
                original_kappa5_squared=6,
                moving_boundary='(-d_T+sqrt(1+t²)*d_z)H/t²=-6*pi_TT',
                brane_velocity_db_dT=str(vel),
                extra_robin_on_dimensionless_H=False,localized_source=False)

def moving_energy_zero_mode():
    ht,hz,grad,v,b=s.symbols('ht hz grad v b',real=True)
    flux=-(ht*hz+v*(ht**2+hz**2+grad**2)/2)/b**3
    assert flux.subs({v:0,hz:0})==0
    assert s.simplify(flux.subs(hz,-v*ht)-v*((1-v**2)*ht**2-grad**2)/(2*b**3))==0
    z=s.symbols('z',positive=True)
    psi=s.Function('psi')(z)
    Q=s.diff(psi,z)+s.Rational(3,2)*psi/z
    H=-s.diff(psi,z,2)+s.Rational(15,4)*psi/z**2
    assert s.simplify(-s.diff(Q,z)+s.Rational(3,2)*Q/z-H)==0
    zero=z**(-s.Rational(3,2))
    assert s.simplify(Q.subs(psi,zero).doit())==0
    assert s.simplify(H.subs(psi,zero).doit())==0
    assert s.integrate(z**(-3),(z,1,s.oo))==s.Rational(1,2)
    return dict(status='PASS moving flux and radial zero-mode counterexample',
                moving_energy_derivative='-b^-3[h_T*h_z+v/2*(h_T²+h_z²+|grad h|²)]',
                moving_neumann='h_z=-v*h_T',
                static_radial_H='Q†Q=-d_z²+15/(4z²)',
                radial_zero_mode='psi=z^-3/2, h=constant',
                strict_gap=False,moving_Green_constructed=False)

def audit():
    return dict(A3=early_thin_receiver(),A4=static_z2_winding(),
                B2=linear_TT_israel(),B3_B5=moving_energy_zero_mode(),
                Agda_kernel_checked=False,physical_graviton_receiver_observed=False)
if __name__=='__main__':
    print(json.dumps(audit(),indent=2,sort_keys=True))
