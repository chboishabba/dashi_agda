"""Signed a posteriori evolution residual for the original split campaign.

A fine affine event and passive Cayley composition is nonexpansive in
normalized state, holding the actual fine material history fixed. The
shadow is a diagnostic, not a second physical trajectory or source.
"""
import numpy as np
from scipy.sparse import issparse,csr_matrix,block_diag,kron,eye

def event_affine(n,r,a,b,V,mass,charge):
    n,r,a,b=map(lambda x:np.asarray(x,float),(n,r,a,b))
    remain=n-r;new=remain+a
    if np.any(remain<0) or np.any(a<0) or np.any(n<0):raise ValueError('invalid event')
    den=np.sqrt(n)*np.sqrt(new)
    coef=np.divide(remain,den,out=np.zeros_like(n),where=den>0)
    shift=np.divide(a,np.sqrt(new),out=np.zeros_like(n),where=new>0)
    shift=(np.sign(charge)*np.sqrt(V*mass)*shift)[:,None]*b
    if np.any(coef>1+1e-14):raise ArithmeticError('noncontractive event')
    return np.repeat(coef,3),shift.ravel()

def field_maps(metric,material):
    L=block_diag([metric[0]['normalized_prolongation'],metric[1]['normalized_prolongation'],
        kron(material['current_prolongation'],eye(9))],format='csr')
    R=block_diag([metric[0]['normalized_restriction'],metric[1]['normalized_restriction'],
        kron(material['current_restriction'],eye(9))],format='csr')
    if not np.allclose((R@L).toarray(),np.eye(L.shape[1]),rtol=1e-12,atol=1e-12):
        raise ArithmeticError('normalized material/field reopening')
    return L,R

def residual_step(actual_fine,shadow_fine,lifted_coarse,previous_bound,shadow_mid,load_rates,dt,coarse_work,fine_work):
    """Real-arithmetic candidate; no outward rounding or material uncertainty."""
    a,b,c=map(lambda x:np.asarray(x,float),(actual_fine,shadow_fine,lifted_coarse))
    if a.shape!=b.shape or b.shape!=c.shape or previous_bound<0 or dt<=0:raise ValueError('invalid residual step')
    r=b-c;err=a-c
    bound=previous_bound+float(np.linalg.norm(r))
    mid=np.asarray(shadow_mid,float);rates=np.asarray(load_rates,float)
    if rates.shape!=mid.shape or np.any(rates<0):raise ValueError('invalid receiver')
    shadow_work=dt*float(rates@(mid*mid))
    weighted=np.sqrt(rates)*mid
    eps=np.sqrt(float(np.max(rates,initial=0.)))*previous_bound
    work_bound=abs(shadow_work-coarse_work)+dt*(2*np.linalg.norm(weighted)*eps+eps*eps)
    # Numerical comparisons deliberately not used as rigorous rounding bounds.
    if np.linalg.norm(err)>bound+1e-10*max(1.,np.linalg.norm(a),np.linalg.norm(c)):
        raise ArithmeticError('evolution residual inequality failed')
    if abs(fine_work-coarse_work)>work_bound+1e-10*max(1.,abs(fine_work),abs(coarse_work)):
        raise ArithmeticError('receiver residual inequality failed')
    return dict(signed_step_residual=r.tolist(),signed_endpoint_error=err.tolist(),
        endpoint_error=float(np.linalg.norm(err)),error_bound_candidate=bound,
        shadow_work_J=shadow_work,coarse_work_J=float(coarse_work),fine_work_J=float(fine_work),
        work_error_bound_candidate_J=float(work_bound),outward_rounding_certified=False)

def coefficient_reopen(fine,coarse,L,R):
    fine,coarse=np.asarray(fine,float),np.asarray(coarse,float)
    if fine.shape[:-1]!=coarse.shape[:-1] or fine.shape[-1]!=L.shape[0] or coarse.shape[-1]!=L.shape[1]:
        raise ValueError('unaligned coefficient histories')
    def apply(a,M):
        return np.asarray(a.reshape(-1,a.shape[-1])@M.T).reshape(a.shape[:-1]+(M.shape[0],))
    restriction=apply(fine,R);rho=restriction-coarse;detail=fine-apply(restriction,L)
    reopened=apply(coarse+rho,L)+detail
    if not np.allclose(reopened,fine,rtol=1e-12,atol=1e-12):raise ArithmeticError('coefficient fibre lost')
    return dict(signed_residual=rho,complement=detail,reconstruction_error=float(np.max(abs(reopened-fine))),
        physical_admission=False)
