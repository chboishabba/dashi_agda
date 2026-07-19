"""Simple-spectrum hard top-eigenvector alignment derivatives."""
from __future__ import annotations
from typing import Any
import numpy as np
from ns_galerkin_coherence_core import (curl_from_gradient,galerkin_packet_rhs_components,
                                        spectral_gradient,strain_from_gradient)

def hard_component_density(eigenvalues:np.ndarray,eigenvectors:np.ndarray,
                           omega:np.ndarray,omega_dot:np.ndarray,
                           strain_dot:np.ndarray,gap_relative_floor:float)->tuple[np.ndarray,np.ndarray]:
    """Return N1-dot density and simple-spectrum mask.

    N1 density is (omega.e1)^2. The formula contains products
    (omega.e1)(omega.ej)(ej^T Sdot e1), hence it is invariant under independent
    sign changes of every eigenvector.
    """
    projections=np.einsum('...ji,...j->...i',eigenvectors,omega)
    omega_dot_projection=np.einsum('...j,...j->...',eigenvectors[..., :,0],omega_dot)
    b=np.einsum('...ia,...ij,...jb->...ab',eigenvectors,strain_dot,eigenvectors)
    scale=np.sqrt(np.sum(eigenvalues*eigenvalues,axis=-1));g12=eigenvalues[...,0]-eigenvalues[...,1];g13=eigenvalues[...,0]-eigenvalues[...,2];floor=gap_relative_floor*scale+1e-30
    simple=(g12>floor)&(g13>floor)
    rotation=np.zeros_like(g12);rotation[simple]=projections[...,1][simple]*b[...,1,0][simple]/g12[simple]+projections[...,2][simple]*b[...,2,0][simple]/g13[simple]
    density=np.zeros_like(g12);density[simple]=2*projections[...,0][simple]*(omega_dot_projection[simple]+rotation[simple])
    return density,simple

def hard_simple_alignment_derivative(raw_hat:np.ndarray,nu:float,target_shell:int,*,gap_relative_floor:float=1e-4)->dict[str,Any]:
    rhs=galerkin_packet_rhs_components(raw_hat,nu,target_shell);wave=rhs['wave'];grad=spectral_gradient(rhs['packet_hat'],wave);strain=strain_from_gradient(grad);omega=curl_from_gradient(grad);omega2=np.sum(omega*omega,axis=-1);E=float(np.mean(omega2))
    if E<=1e-30:raise ValueError('zero packet enstrophy')
    values,vectors=np.linalg.eigh(strain);values=values[...,::-1];vectors=vectors[..., :,::-1];w1=np.einsum('...j,...j->...',vectors[..., :,0],omega);N=float(np.mean(w1*w1));A=N/E
    rows={};total_E=total_N=total_A=0.;mask_reference=None
    for name,hat in rhs['components'].items():
        dot_grad=spectral_gradient(hat,wave);omega_dot=curl_from_gradient(dot_grad);strain_dot=strain_from_gradient(dot_grad);density,mask=hard_component_density(values,vectors,omega,omega_dot,strain_dot,gap_relative_floor);mask_reference=mask
        Edot=float(2*np.mean(np.einsum('...i,...i->...',omega,omega_dot)));Ndot=float(np.mean(density));Adot=(Ndot*E-N*Edot)/(E*E);rows[name]={'enstrophy_derivative':Edot,'hard_alignment_numerator_derivative_simple_spectrum':Ndot,'hard_normalized_alignment_derivative_simple_spectrum':Adot,'parabolic_normalized_hard_alignment_derivative_simple_spectrum':Adot/(nu*2**(2*target_shell))};total_E+=Edot;total_N+=Ndot;total_A+=Adot
    return {'hard_packet_enstrophy_E':E,'hard_alignment_numerator_N1':N,'hard_alignment_A1':A,'simple_spectrum_grid_fraction':float(np.mean(mask_reference)) if mask_reference is not None else 0.,'component_derivatives':rows,'component_sum_enstrophy_derivative':total_E,'component_sum_hard_numerator_derivative':total_N,'component_sum_hard_alignment_derivative':total_A,'gap_relative_floor':gap_relative_floor,'gauge_invariant_under_independent_eigenvector_signs':True,'global_derivative_authority':False,'reason':'hard top eigenvector is not differentiable at eigenvalue collisions; values are simple-spectrum restricted'}
