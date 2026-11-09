"""Reusable Marchenko-Pastur numerical null for PNF and financial panels.
IID MP is an asymptotic baseline, not semantic authority, a finite p-value,
or a guarantee of economic alpha. Rows are observations; columns are features.
"""
from dataclasses import dataclass
import numpy as np

@dataclass(frozen=True)
class MPNull:
    gamma: float
    variance: float = 1.0

    def __post_init__(self):
        if not (np.isfinite(self.gamma) and self.gamma > 0):
            raise ValueError("positive finite aspect ratio required")
        if not (np.isfinite(self.variance) and self.variance > 0):
            raise ValueError("positive finite variance required")

    @property
    def edges(self):
        t = np.sqrt(self.gamma)
        return (self.variance*(1-t)**2, self.variance*(1+t)**2)

    @property
    def zero_atom(self):
        return max(0.0, 1-1/self.gamma)

    def density(self, x):
        x = np.asarray(x, dtype=float)
        lo, hi = self.edges
        result = np.zeros_like(x)
        valid = (x > max(lo, 0)) & (x < hi)
        z = x[valid]
        result[valid] = np.sqrt(np.maximum(0,(hi-z)*(z-lo))) / (
            2*np.pi*self.gamma*self.variance*z)
        return result

def covariance(x, correlation=True):
    a = np.asarray(x, dtype=float)
    if a.ndim != 2 or a.shape[0] < 2 or a.shape[1] < 1 or not np.isfinite(a).all():
        raise ValueError("need finite n>=2 by p>=1 panel")
    a = a-a.mean(axis=0)
    c = (a.T@a)/(a.shape[0]-1)
    if correlation:
        d = np.diag(c)
        if np.any(d <= 0):
            raise ValueError("constant source column")
        c = c/np.sqrt(np.outer(d,d))
    return (c+c.T)/2

def clean(c, mp, correlation=True):
    c = np.asarray(c, dtype=float)
    if c.ndim != 2 or c.shape[0] != c.shape[1] or not np.isfinite(c).all():
        raise ValueError("finite square operator required")
    if not np.allclose(c,c.T,atol=1e-10):
        raise ValueError("symmetric operator required")
    w,v = np.linalg.eigh((c+c.T)/2)
    if np.min(w) < -1e-8:
        raise ValueError("original covariance not PSD")
    w = np.maximum(w,0)
    lo,hi = mp.edges
    bulk = (w >= lo)&(w <= hi)&(w > 1e-12)
    f = w.copy()
    if bulk.any():
        f[bulk] = np.mean(w[bulk])
    out = (v*f)@v.T
    defect = float(np.max(np.abs(np.diag(out)-1)))
    if correlation:
        d = np.diag(out)
        if np.any(d <= 0):
            raise ValueError("cannot normalize nonpositive diagonal")
        out = out/np.sqrt(np.outer(d,d))
    out = (out+out.T)/2
    return out, {"bulk_modes":int(bulk.sum()),
                 "forced_zero_modes_observed":int((w <= 1e-12).sum()),
                 "diagonal_error_before_rescale":defect,
                 "trace_preserved_before_rescale":bool(np.isclose(w.sum(),f.sum()))}

def receipt(x, source, measurement, correlation=True):
    if not source or not measurement:
        raise ValueError("source and measurement kind are required")
    a = np.asarray(x,dtype=float)
    c = covariance(a,correlation)
    n,p = a.shape
    mp = MPNull(p/(n-1), 1 if correlation else float(np.trace(c)/p))
    lo,hi = mp.edges
    eig = np.linalg.eigvalsh(c)
    filtered, detail = clean(c,mp,correlation)
    return {"source":source,"measurement":measurement,"n":n,"p":p,
            "gamma":mp.gamma,"variance":mp.variance,
            "mp_lower":lo,"mp_upper":hi,"mp_zero_atom":mp.zero_atom,
            "forced_zero_min":max(0,p-n+1),
            "zero_modes":int((eig < 1e-9).sum()),
            "above_edge":int((eig > hi).sum()),
            "below_positive_edge":int(((eig > 1e-9)&(eig < lo)).sum()),
            "trace":float(np.trace(c)),
            "cleaned_psd":bool(np.linalg.eigvalsh(filtered)[0] >= -1e-8),
            "cleaned_unit_diagonal":bool(np.allclose(np.diag(filtered),1))
                if correlation else None,
            "cleaning":detail,
            "status":"candidate_only; source-specific null and finite-sample calibration unpaid"}
