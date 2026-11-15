#!/usr/bin/env python3
"""Original AdS5 moving boundary: constant-spatial-coefficient TT prepotential.

L=-dT²+dz²-(3/z)dz+Delta_3, B=(1-v²)dy+v dT|y.
The local constant-coefficient TT operator S commutes with L and B
because they have no spatial dependence in the 3 homogeneous brane
directions. This is not a full receiver/Weyl convergence claim.
"""
import json
import sympy as s

def fourier_symbol():
    x,y,z=s.symbols('kx ky kz',real=True)
    k=s.Matrix([x,y,z]);sq=(k.T*k)[0]
    P=sq*s.eye(3)-k*k.T
    Q=s.diag(0,1,-1)
    S=P*Q*P-s.Rational(1,2)*P*s.trace(P*Q)
    assert all(s.factor(el)==0 for el in k.T*S)
    assert s.factor(s.trace(S))==0
    assert s.factor(S[1,1].subs({y:0,z:0}))==x**4
    return dict(general_3d_fourier_transversality_exact=True,
       general_3d_tracefree_exact=True,k_along_x_TT_yy_symbol='kx^4',
       local_fourth_order_polynomial=True,no_singular_k_inverse=True)

def commute_operator():
    T,z,x,y,w=s.symbols('T z x y w',real=True)
    v=s.Function('v')(T)
    f=s.exp(-T*T-z*z)*(x**7+2*x*y*y*z+w**5*y+x*y*z*w)
    lap=lambda a:s.diff(a,x,2)+s.diff(a,y,2)+s.diff(a,w,2)
    def tt(a):
        def p(i,j,b):return -int(i==j)*lap(b)+s.diff(b,(x,y,w)[i],(x,y,w)[j])
        return p(1,1,p(1,1,a))-p(1,2,p(2,1,a))-s.Rational(1,2)*p(1,1,p(1,1,a)-p(2,2,a))
    L=lambda a:-s.diff(a,T,2)+s.diff(a,z,2)-3*s.diff(a,z)/z+lap(a)
    B=lambda a:(1-v**2)*s.diff(a,z)+v*s.diff(a,T)
    assert s.simplify(L(tt(f))-tt(L(f)))==0
    assert s.simplify(B(tt(f))-tt(B(f)))==0
    return dict(verify_nonseparable_test_function=True,
       original_5d_L_commutes_with_spatial_TT=True,
       original_moving_oblique_boundary_B_commutes_with_spatial_TT=True,
       formal_universal_reason='commuting spatial mixed partials and spatially homogeneous L/B coefficients',
       full_3D_receiver_and_both_Weyl_nonzero_proved=False)

def report():return dict(symbol=fourier_symbol(),operators=commute_operator(),
    bridge='L Psi=0, B Psi=g -> L(S Psi)=0, B(S Psi)=S g',
    generating_matter_action_supplied=False)

if __name__=='__main__':print(json.dumps(report(),indent=2))
