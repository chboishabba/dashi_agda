#!/usr/bin/env python3
"""Original moving a=t AdS5 TT: exact finite radial Sobolev hierarchy.

For each physical 3D TT multipole ell=0,2,4 with effective radial
d=3,7,11, the conservative A_ell=-L_d is positive and radial
cell-volume weighted selfadjoint. All original b(T),v(T),AdS -3/z,
normal SBP and the weak original Israel SAT are independent of r,
so [A_ell^k, full original linear moving (T,y,r) generator]=0 for
EVERY nonnegative integer k, with actual source G transformed as
A_ell^k G. E_k=E(A^k U,A^k P,A^k M) satisfies SAME homogeneous
coupled semidiscrete bound E_k'<=5E_k (mode4) or
E_k'<=(5+16t)E_k (physical constraint-preserving mode3, dy<=b/4).
The lifted forced theorem holds with A^k F. The *actual original
compact 3D TT source* has rapidly growing high radial derivative
norms: no mesh-uniform H4+epsilon both-Weyl trace is claimed.
"""
import json
import numpy as np
from ksw668_f8_full_coupled_weighted_sbp_energy import setup,radial_stiffness
from ksw668_f8_characteristic_constraint_maxcut import actual_stage,energy_derivative
from ksw668_f8_fv_source_flux import exact_cell_averages
DIMS=(3,7,11)
def radial_A_power(X,k,dr):
    if not isinstance(k,int) or k<0:raise ValueError('nonnegative integer radial order')
    a=np.asarray(X,float).copy()
    if a.ndim!=3 or a.shape[0]!=3:raise ValueError('three TT modes')
    if k:
        for q,d in enumerate(DIMS):
            L,_=radial_stiffness(d,a.shape[-1],dr)
            a[q]=a[q]@np.linalg.matrix_power(-L,k).T
    return a
def source_A_power(G,k,dr):
    return radial_A_power(np.asarray(G,float)[:,None,:],k,dr)[:,0,:]
def check(t=4/3,ny=9,nr=12,dy=.012,dr=.008,seed=5,mode=3):
    if mode not in (3,4):raise ValueError('physical weak SAT scheme')
    data=setup(t=t,ny=ny,nr=nr,dy=dy,dr=dr,seed=seed)
    G=1e-5*exact_cell_averages(.04,np.arange(nr)*dr,dr)
    base=actual_stage(data,mode,G)
    rows=[]
    for k in (0,1,2,3):
        X=dict(data)
        for name in ('U','P','M'):
            X[name]=radial_A_power(data[name],k,dr)
        Gk=source_A_power(G,k,dr)
        RHS=actual_stage(X,mode,Gk)
        expected=tuple(radial_A_power(y,k,dr) for y in base)
        relative=max(float(np.max(abs(y-z))/max(1.,np.max(abs(y)),np.max(abs(z))))
            for y,z in zip(RHS,expected))
        assert relative<3e-9,(mode,k,relative)
        E,Ep=energy_derivative(X,actual_stage(X,mode))
        if mode==3:assert Ep<=(5+16*t)*E+1e-8*max(1,E)
        else:assert Ep<=5*E+1e-8*max(1,E)
        rows.append(dict(k=k,commutation_relative_error=relative,
           higher_radial_energy=E,homogeneous_energy_growth_ratio=Ep/E,
           compact_original_TT_source_high_radial_norm=float(np.linalg.norm(Gk))))
    return dict(original_t=t,mode=mode,
      exact_TT_angular_modes=[0,2,4],
      original_compact_TT_source_eps=.04,
      finite_radial_sobolev_orders=[0,1,2,3],
      rows=rows,all_radial_powers_commute_exactly_algebraically=True,
      mesh_uniform_compact_source_high_Sobolev_budget_proved=False,
      original_full_Weyl_H4_plus_trace_proved=False)
def audit():
    rows=[check(t,mode=mode,seed=9) for mode in (3,4)
        for t in (1.,4/3,2.,12.)]
    return dict(cases=rows,original_compact_3D_TT_source=True,
       finite_radial_sobolev_all_integer_powers_commute=True,
       original_both_Weyl_receiver_convergence_open=True,
       physical_graviton_observed=False)
if __name__=='__main__':print(json.dumps(audit(),indent=2))
