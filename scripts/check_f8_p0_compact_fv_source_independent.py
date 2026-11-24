"""F8 P0 original compact TT FV source: independent source-function quadrature.

Compare the ORIGINAL exact_cell_averages primitive integral against a separate
200-point Gaussian quadrature of the fourth-derivative profiles defined in
the ORIGINAL ksw668_f8_tt_multipole source. Finite source consistency test,
not a continuum solver convergence proof or independent physical TT source.
"""
import json
import numpy as np
from scipy.special import roots_legendre
from ksw668_f8_fv_source_flux import exact_cell_averages
from ksw668_f8_tt_multipole import profiles

def audit():
    x,w=roots_legendre(200)
    ps=profiles()
    assert [ell for ell,fn,origin in ps]==[0,2,4]
    rows=[]
    for dr in (.04,.03,.025,.01,.008,.006):
        nr=round(3/dr)+1
        rgrid=dr*np.arange(nr)
        exact=exact_cell_averages(.04,rgrid,dr)
        independent=np.zeros_like(exact)
        for j,R in enumerate(rgrid):
            lo=max(0.,R-dr/2)
            hi=min(.04,R+dr/2)
            if hi<=lo:
                continue
            rr=lo+(hi-lo)*(x+1)/2
            u=rr/.04
            for i,(ell,fn,origin) in enumerate(ps):
                d=3+2*ell
                volume=((R+dr/2)**d-lo**d)/d
                independent[i,j]=(hi-lo)/2*np.dot(w,rr**(d-1)*fn(u))/volume
        err=float(np.max(abs(exact-independent)))
        scale=max(1.,float(np.max(abs(exact))),float(np.max(abs(independent))))
        relative=err/scale
        assert relative<1e-7,(dr,relative)
        assert np.all(exact[:,rgrid>=.04+dr/2]==0)
        volumes=[]
        for ell in (0,2,4):
            d=3+2*ell
            V=(((rgrid+dr/2)**d-(np.maximum(rgrid-dr/2,0))**d)/d)
            volumes.append(V)
        l2=[float(np.sqrt(np.dot(volumes[i],exact[i]**2))) for i in range(3)]
        rows.append(dict(dr=dr,nr=nr,relative_max_source_cell_error=relative,
                    max_abs_source_coeff_by_mode=np.max(abs(exact),axis=1).tolist(),
                    weighted_radial_l2_by_mode=l2,
                    nonzero_cell_count=int(np.count_nonzero(exact[0]))))
    return dict(status='PASS original exact-FV versus independent 200-node source-profile quadrature',
                rows=rows,
                max_relative_quadrature_discrepancy=max(r['relative_max_source_cell_error'] for r in rows),
                interpretation='Source coefficients highly mesh-dependent at eps=.04; this is NOT evidence primitive integration is incorrect, nor proof that evolving original source is continuum-resolved.')
if __name__=='__main__':
    print(json.dumps(audit(),indent=2))
