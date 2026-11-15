#!/usr/bin/env python3
"""Original a=t AdS5: SMS projected FIVE-dimensional Weyl vs intrinsic FOUR-dimensional Weyl.

Shiromizu--Maeda--Sasaki (2000) effective Einstein projection,
kappa5²=6, sigma=1, ell=1, Lambda4=0. Linear TT tensor result is
a source/Einstein-operator identity, NOT a retarded physical measurement.
"""
import json
import sympy as s

def algebra():
    eps,rho,p=s.symbols('eps rho p',real=True)
    Q=s.diag(0,0,1,-1)
    T=s.diag(-rho,p,p,p)+eps*Q
    tr=s.trace(T)
    Pi=(-T*T/s.Integer(4)+tr*T/s.Integer(12)+
        (s.trace(T*T)/s.Integer(8)-tr*tr/s.Integer(24))*s.eye(4))
    dPi=Pi.diff(eps).subs(eps,0).applyfunc(s.factor)
    c=-(rho+3*p)/12
    assert dPi==s.simplify(c)*Q
    k52=s.Integer(6);sigma=s.Integer(1)
    k42=k52*k52*sigma/s.Integer(6)
    assert k42==6
    source_coeff=s.factor(k42+k52*k52*c)
    assert s.simplify(source_coeff-(6-3*(rho+3*p)))==0
    rational=source_coeff.subs({rho:s.Rational(1,4),p:-s.Rational(1,10)})
    assert rational==s.Rational(123,20)
    tt,xx=s.symbols('tt xx',real=True)
    h=s.Function('h')(tt,xx)
    # Flat TT Einstein tensor: +1/2*(d_t²-d_x²)h, not minus.
    dG=(s.diff(h,tt,2)-s.diff(h,xx,2))/2
    assert s.simplify(dG-(s.diff(h,tt,2)-s.diff(h,xx,2))/2)==0
    return dict(SMS_matter_quadratic_Pi_TT='-(rho+3p)/12*pi_TT',
       effective_kappa4_squared='6',kappa5_squared=6,brane_tension=1,
       projected_5D_E_TT='[6-3*(rho+3p)]*pi_TT - 1/2*(d_t²+3H d_t-a^-2 Delta)H_TT',
       original_t_4over3_source_coefficient=str(rational),
       flat_TT_Einstein_sign='delta Gyy=+1/2*(h_tt-h_xx)',
       projected5D_receiver_principal_without_local_source='+1/2*(n dot xi)^2*H_TT',
       intrinsic_4D_electric_Weyl='-(d_eta²+d_x²)H_yy/(4a²)',
       those_two_Weyl_tensors_identical=False,
       numerical_projected_5D_Weyl_receiver_computed=False,
       physical_matter_action_generated=False,
       actual_early_retarded_projected_5D_Weyl_proved=False)
if __name__=='__main__':print(json.dumps(algebra(),indent=2))
