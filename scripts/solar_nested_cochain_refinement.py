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
