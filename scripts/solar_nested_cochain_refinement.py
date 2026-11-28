"""Exact signed cochain refinement of the ORIGINAL tetrahedral shell complex.

Barycentric subdivision is nested in the piecewise-flat parent, unlike the
independently radially projected angular meshes. Integer numerators carry
Whitney prolongation, oriented chain sums carry restriction. No identification
of these two mesh families or physical continuum convergence is made.
"""
from itertools import combinations,permutations
import numpy as np
from scipy.sparse import csr_matrix,eye

def sign(p):
    return (-1)**sum(p[i]>p[j] for i in range(len(p)) for j in range(i+1,len(p)))

def determinant(a):
    n=len(a)
    return sum(sign(p)*int(np.prod([a[i][p[i]] for i in range(n)],dtype=np.int64))
               for p in permutations(range(n)))

def incidence(s):
    maps=[{t:i for i,t in enumerate(row)} for row in s]
    out=[]
    for k in range(3):
        rows=[];cols=[];data=[]
        for i,t in enumerate(s[k+1]):
            for j in range(len(t)):
                rows.append(i);cols.append(maps[k][t[:j]+t[j+1:]]);data.append((-1)**j)
        out.append(csr_matrix((data,(rows,cols)),shape=(len(s[k+1]),len(s[k])),dtype=np.int64))
    return out

def exact_zero(A):
    A=A.tocsr();A.eliminate_zeros();return A.nnz==0

def nested_cochains(xyz,s):
    """Return actual nested geometry and exact integer cochain maps all degrees.

    Each fine vertex is the barycenter of its original face. For an oriented
    fine simplex the Whitney k-form integral is the determinant of the
    corresponding barycentric coordinates. Common denominator 12^(k+1).
    """
    xyz=np.asarray(xyz,float)
    s=[list(map(tuple,row)) for row in s]
    if len(s)!=4 or xyz.shape!=(len(s[0]),3) or s[0]!=[(i,) for i in range(len(xyz))]:
        raise ValueError('invalid original simplicial complex')
    if any(tuple(sorted(t))!=t or len(t)!=k+1 for k,row in enumerate(s) for t in row):
        raise ValueError('original simplex orientation must use ascending vertex IDs')
    owners=[t for row in s for t in row]; ids={t:i for i,t in enumerate(owners)}
    if len(ids)!=len(owners):raise ValueError('duplicate original simplex')
    fine_xyz=np.array([xyz[list(t)].mean(axis=0) for t in owners])
    def flag(p):
        return tuple(ids[tuple(sorted(p[:j+1]))] for j in range(len(p)))
    fine=[sorted({flag(p) for t in s[3] for p in permutations(t)})]
    tets=fine[0]
    fine=[[(i,) for i in range(len(owners))]]+[sorted({v for t in tets for v in combinations(t,k+1)}) for k in (1,2)]+[tets]
    R=[];N=[];den=[]
    for k in range(4):
        coarse_ids={t:i for i,t in enumerate(s[k])}
        fine_ids={t:i for i,t in enumerate(fine[k])}
        rr=[];rc=[];rv=[]
        for i,t in enumerate(s[k]):
            for p in permutations(t):
                rr.append(i);rc.append(fine_ids[flag(p)]);rv.append(sign(p))
        R.append(csr_matrix((rv,(rr,rc)),shape=(len(s[k]),len(fine[k])),dtype=np.int64))
        lr=[];lc=[];lv=[]
        for i,f in enumerate(fine[k]):
            carrier=owners[f[-1]]
            for t in combinations(carrier,k+1):
                a=[[12//len(owners[v]) if w in owners[v] else 0 for w in t] for v in f]
                z=determinant(a)
                if z:lr.append(i);lc.append(coarse_ids[t]);lv.append(z)
        N.append(csr_matrix((lv,(lr,lc)),shape=(len(fine[k]),len(s[k])),dtype=np.int64))
        den.append(12**(k+1))
    Dc=incidence(s);Df=incidence(fine)
    for k in range(4):
        if not exact_zero(R[k]@N[k]-den[k]*eye(len(s[k]),dtype=np.int64,format='csr')):
            raise ArithmeticError('restriction/prolongation not identity')
    for k in range(3):
        if not exact_zero(R[k+1]@Df[k]-Dc[k]@R[k]):
            raise ArithmeticError('restriction incidence square')
        if not exact_zero(12*(Df[k]@N[k])-N[k+1]@Dc[k]):
            raise ArithmeticError('Whitney prolongation incidence square')
    return dict(xyz=fine_xyz,simplices=fine,restriction=R,numerator=N,denominator=den,
        coarse_incidence=Dc,fine_incidence=Df,carrier=owners,
        exact_cochain_squares=6,exact_reopen_degrees=4,physical_admission=False)

def signed_coefficient_complement(bundle,k,fine,coarse):
    """Independent coefficient fibres; reconstruct every signed residual."""
    R=bundle['restriction'][k];L=bundle['numerator'][k]/bundle['denominator'][k]
    fine=np.asarray(fine,float);coarse=np.asarray(coarse,float)
    if fine.shape[-1]!=R.shape[1] or coarse.shape!=fine.shape[:-1]+(R.shape[0],):
        raise ValueError('refinement state shape mismatch')
    y=np.asarray(fine@R.T); detail=fine-np.asarray(y@L.T); residual=y-coarse
    reopened=np.asarray((coarse+residual)@L.T)+detail
    if not np.allclose(reopened,fine,rtol=1e-12,atol=1e-12):
        raise ArithmeticError('signed refinement reopen failed')
    return dict(signed_residual=residual,spatial_complement=detail,reconstruction_error=float(np.max(abs(reopened-fine))))

def metric_pullback(bundle,coarse_masses,fine_masses):
    """Actual consistent Whitney Hodge pullback and diagonal-metric defect.
    The signed maps act on raw cochains, never directly on energy coordinates.
    """
    receipts=[]
    for k,H,F in zip((1,2),coarse_masses,fine_masses):
        L=bundle['numerator'][k]/bundle['denominator'][k]
        R=bundle['restriction'][k]
        H,F=np.asarray(H,float),np.asarray(F,float)
        if H.shape!=(L.shape[1],)*2 or F.shape!=(L.shape[0],)*2:
            raise ValueError('Hodge and cochain shape mismatch')
        if np.any(np.diag(H)<=0) or np.any(np.diag(F)<=0):
            raise ValueError('nonpositive Hodge diagonal')
        pull=L.T@(F@L)
        diag_pull=L.T@(L.multiply(np.diag(F)[:,None]))
        diag_defect=diag_pull.toarray()-np.diag(np.diag(H))
        # Normalized maps for the original diagonal-Hodge candidate.
        Ln=L.multiply(np.sqrt(np.diag(F))[:,None]).multiply(1/np.sqrt(np.diag(H))[None,:])
        Rn=R.multiply(np.sqrt(np.diag(H))[:,None]).multiply(1/np.sqrt(np.diag(F))[None,:])
        if not np.allclose((Rn@Ln).toarray(),np.eye(H.shape[0]),rtol=1e-12,atol=1e-12):
            raise ArithmeticError('normalized cochain reopen failed')
        receipts.append(dict(degree=k,consistent_relative_defect=float(np.linalg.norm(pull-H)/np.linalg.norm(H)),
            diagonal_relative_defect=float(np.linalg.norm(diag_defect)/np.linalg.norm(np.diag(H))),
            normalized_prolongation=Ln.tocsr(),normalized_restriction=Rn.tocsr()))
    return receipts

def endpoint_time_complement(bundle,k,fine,coarse):
    """Nonperiodic nested endpoint grids, independent space/time transport.
    Leading axis is time; intermediate axes can carry base/first/second jets.
    Retain signed omitted endpoints rather than use periodic Fourier here.
    """
    fine,coarse=np.asarray(fine,float),np.asarray(coarse,float)
    if len(coarse)==0 or len(fine)%len(coarse):
        raise ValueError('nested endpoint grids required')
    R=bundle['restriction'][k];L=bundle['numerator'][k]/bundle['denominator'][k]
    if fine.ndim<2 or coarse.shape[1:-1]!=fine.shape[1:-1] or fine.shape[-1]!=R.shape[1] or coarse.shape[-1]!=R.shape[0]:
        raise ValueError('coefficient history shape mismatch')
    def apply(x,M):
        return np.asarray(x.reshape(-1,x.shape[-1])@M.T).reshape(x.shape[:-1]+(M.shape[0],))
    y=apply(fine,R);spatial=fine-apply(y,L)
    stride=len(fine)//len(coarse); ix=np.arange(stride-1,len(fine),stride)
    signed=y[ix]-coarse; temporal=y.copy();temporal[ix]=0.
    z=temporal.copy();z[ix]=coarse+signed
    reconstructed=apply(z,L)+spatial
    square=y[ix]-apply(fine[ix],R)
    if not np.allclose(reconstructed,fine,rtol=1e-12,atol=1e-12) or np.any(square!=0):
        raise ArithmeticError('indexed space-time reopening failed')
    return dict(signed_residual=signed,spatial_complement=spatial,temporal_complement=temporal,
        zero_mode=y.mean(axis=0),square_residual=square,
        reconstruction_error=float(np.max(abs(reconstructed-fine))))
