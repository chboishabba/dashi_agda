"""Storage helpers for the SAME indexed matrix operator, dense or sparse."""
import numpy as np
from scipy.sparse import issparse,csr_matrix,diags

def matrix(a):
    if issparse(a):
        a=csr_matrix(a,dtype=float,copy=True);a.sum_duplicates();a.eliminate_zeros();return a
    return np.asarray(a,float)

def finite(a):
    return bool(np.isfinite(a.data if issparse(a) else a).all())

def block(a,ix):
    return a[ix,:][:,ix].toarray() if issparse(a) else a[np.ix_(ix,ix)]

def close(a,b,rtol=1e-5,atol=1e-8):
    if not (issparse(a) or issparse(b)):return np.allclose(a,b,rtol=rtol,atol=atol)
    a,b=csr_matrix(a),csr_matrix(b)
    d=(a-b).tocoo();d.eliminate_zeros()
    if not d.nnz:return True
    v=np.asarray(b[d.row,d.col]).ravel()
    return bool(np.all(abs(d.data)<=atol+rtol*abs(v)))

def nonzero_pairs(a,site):
    i,j=a.nonzero()
    return {(min(int(u),int(v)),max(int(u),int(v))) for u,v in zip(i,j) if site[u]!=site[v]}

def diagonal(a,sparse=False):
    return diags(a,format='csr') if sparse else np.diag(a)
