"""Finite metric Maxwell cochain weld, signed observation and passive bound.
Uses oriented incidence and positive diagonal Hodge masses. Numerical
consumer of the repository Stokes/Cayley owners, not continuum convergence.
"""
import numpy as np

def metric_curl(d0,d1,d2,me,mh):
    d0,d1,d2=map(np.asarray,(d0,d1,d2))
    if not all(np.all(np.isin(a,[-1,0,1])) for a in (d0,d1,d2)):
        raise ValueError('signed incidence required')
    from scipy.sparse import csr_matrix
    p=csr_matrix(d1)@csr_matrix(d0);q=csr_matrix(d2)@csr_matrix(d1)
    p.eliminate_zeros();q.eliminate_zeros()
    if p.nnz or q.nnz:
        raise ValueError('boundary of boundary is nonzero')
    me,mh=map(lambda a:np.asarray(a,float),(me,mh))
    if me.shape!=(d1.shape[1],) or mh.shape!=(d1.shape[0],) or np.any(me<=0) or np.any(mh<=0):
        raise ValueError('positive Hodge mass required')
    # E is primal edge circulation; magnetic flux is primal face cochain.
    # xE=sqrt(me)*E, xB=sqrt(mh)*B, B'=-d1 E.
    C=np.sqrt(mh)[:,None]*d1/np.sqrt(me)[None,:]
    K=np.block([[np.zeros((len(me),len(me))),C.T],[-C,np.zeros((len(mh),len(mh)))]])
    assert np.array_equal(K,-K.T)
    return K

def observation(K,P,L):
    K,P,L=map(lambda x:np.asarray(x,float),(K,P,L))
    if not np.allclose(P@L,np.eye(len(P))): raise ValueError('right inverse')
    Q=np.eye(len(K))-L@P
    reduced=P@K@L
    defect=P@K-reduced@P
    assert np.allclose(defect,P@K@Q)
    return reduced,defect,Q

def recover(x,P,L):
    x=np.asarray(x); coarse=P@x; residual=x-L@coarse
    assert np.allclose(P@residual,0) and np.allclose(L@coarse+residual,x)
    return coarse,residual

def passive_certificate(useful,loss,source):
    """Relaxation valid for all trajectories sharing these quadratic forms.
    If total loss >= alpha*useful, then restored passive useful <=
    incident/(1+alpha). PSD certificate must be checked on whole state.
    """
    U,R=map(lambda a:np.asarray(a,float),(useful,loss))
    assert U.shape==R.shape and U.ndim==2 and U.shape[0]==U.shape[1]
    assert np.allclose(U,U.T) and np.allclose(R,R.T)
    assert np.linalg.eigvalsh(U)[0]>=0 and np.linalg.eigvalsh(R)[0]>=0
    assert source>=0
    if np.linalg.norm(U)==0:return dict(alpha=0.,upper_J=0.)
    lo=0.; hi=1.
    def valid(a):return np.linalg.eigvalsh(R-a*U)[0]>=0
    for _ in range(40):
        if not valid(hi):break
        hi*=2
    for _ in range(60):
        mid=(lo+hi)/2
        if valid(mid):lo=mid
        else:hi=mid
    return dict(alpha=lo,upper_J=source/(1+lo),min_eigenvalue=float(np.linalg.eigvalsh(R-lo*U)[0]),numerical_candidate=True)

def reverse_source_scale(active_useful,passive_useful,paid,target=0.):
    """Exact scalar amplitude-squared reverse solution for frozen linear response.
    Not applicable to source-dependent material or nonlinear source backaction."""
    if min(active_useful,passive_useful,paid,target)<0:raise ValueError('nonnegative work')
    delta=active_useful-passive_useful
    if delta<=0:return dict(feasible=False,margin_per_unit_J=delta)
    return dict(feasible=True,incident_scale_infimum=(paid+target)/delta,strict_gain_requires_greater=True)

def fixtures():
    import sympy as s
    # Oriented tetrahedral boundary, exact chain identities.
    from itertools import combinations
    simplices=[list(combinations(range(4),k)) for k in (1,2,3,4)]
    D=[]
    for low,high in zip(simplices,simplices[1:]):
        a=s.zeros(len(high),len(low))
        for i,t in enumerate(high):
            for j in range(len(t)):a[i,low.index(t[:j]+t[j+1:])]=(-1)**j
        D.append(a)
    assert D[1]*D[0]==s.zeros(4,4) and D[2]*D[1]==s.zeros(1,6)
    K=metric_curl(*[np.array(a).astype(int) for a in D],np.ones(6),np.ones(4))
    P=np.eye(10)[:3]; L=P.T; k,defect,Q=observation(K,P,L)
    x=np.arange(10.); y,r=recover(x,P,L)
    assert np.allclose(P@K@x,k@y+P@K@r)
    b=passive_certificate(np.eye(2),2*np.eye(2),9.)
    assert abs(b['upper_J']-3)<1e-10
    assert reverse_source_scale(4,2,6)['incident_scale_infimum']==3
    return dict(chain_identities=2,skew=True,reconstruction=True,defect=True,passive_bound=b,reverse=True)
if __name__=='__main__':
    import json
    print(json.dumps(fixtures(),indent=2))
