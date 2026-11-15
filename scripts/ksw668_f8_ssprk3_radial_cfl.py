#!/usr/bin/env python3
"""KSW F8 exact frozen RADIAL-only conservative FV SSPRK3 CFL theorem.

Original moving a=t three TT multipoles yield effective d=3,7,11
radial operators. On a homogeneous outer Dirichlet radial test domain,
the exact shell-volume finite-volume L_d is selfadjoint negative in the
physical radial cell-volume weight. The first-order pure-radial wave
system is a weighted skew generator and classical SSPRK3 satisfies
|R(i*x)|²-1=x^4(x²-3)/36. Thus modal stability iff
dt*sqrt(lambda_max(-L_d))<=sqrt(3). Gershgorin supplies a sufficient
all-modes bound lambda_max <=2 max_i(-L_ii).
This is NOT the full moving (T,y,r) RK3/Israel stability theorem.
"""
import json,math
import numpy as np
import sympy as sp
def symbolic():
    x=sp.symbols('x',real=True)
    z=sp.I*x
    R=lambda z:1+z+z**2/2+z**3/6
    formula=sp.factor(sp.expand_complex(R(z)*sp.conjugate(R(z))-1))
    assert sp.simplify(formula-x**4*(x*x-3)/36)==0
    return dict(modulus_square_minus_one='x^4*(x^2-3)/36',
       radial_imaginary_axis_stability_iff='|dt omega|<=sqrt(3)')
def fv_matrix(d,active_cells=50,dr=1.):
    if d not in (3,7,11) or active_cells<4 or dr<=0:
        raise ValueError('original effective 3/7/11 dims, finite cells and positive step')
    n=active_cells; L=np.zeros((n,n))
    for j in range(n):
        if j==0:cp=2*d;cm=0.
        else:
            p=j+.5;m=j-.5;den=p**d-m**d
            cp=d*p**(d-1)/den;cm=d*m**(d-1)/den
        L[j,j]=-(cp+cm)/dr**2
        if j>0:L[j,j-1]=cm/dr**2
        if j<n-1:L[j,j+1]=cp/dr**2
    j=np.arange(n,dtype=float)
    vol=(((j+.5)*dr)**d-(np.maximum(j-.5,0)*dr)**d)/d
    S=np.sqrt(vol)[:,None]*L/np.sqrt(vol)[None,:]
    assert np.allclose(S,S.T,atol=3e-12,rtol=3e-12)
    return L,S,vol
def spectral(d=11,n=50,dr=.01):
    L,S,vol=fv_matrix(d,n,dr)
    lam=float(np.linalg.eigvalsh(-S)[-1])
    diag=2*float(np.max(-np.diag(L)))
    assert 0<lam<=diag*(1+1e-12)
    return dict(d=d,grid_cells=n,
        lambda_max=lam,gershgorin_upper_bound=diag,
        sufficient_dt_over_dr=math.sqrt(3/diag)/dr,
        sharp_this_radial_mesh_dt_over_dr=math.sqrt(3/lam)/dr)
def mode_energy_growth(lam,dt):
    z=1j*dt*math.sqrt(lam)
    R=1+z+z*z/2+z*z*z/6
    return abs(R)**2
def audit():
    rows=[spectral(d) for d in (3,7,11)]
    counterexample=mode_energy_growth(rows[-1]['lambda_max'],.45*.01)
    assert counterexample>1.8
    assert rows[-1]['sufficient_dt_over_dr']<.27
    return dict(symbolic=symbolic(),radial_modes=rows,
      existing_dt_over_dr_045_can_amplify_radial_mode=True,
      radial_11d_045_one_step_energy_growth=counterexample,
      pure_radial_SSPRK3_spectral_CFL_closed=True,
      original_full_moving_Israel_SSPRK3_CFL_accepted=False,
      original_receiver_both_Weyl_converged=False)
if __name__=='__main__':print(json.dumps(audit(),indent=2))
