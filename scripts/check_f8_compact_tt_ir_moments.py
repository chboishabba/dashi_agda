"""Original compact TT continuum versus shell-projected IR moments.
No identification of the piecewise constant Fourier transform with native FV modes.
"""
import json
import numpy as np
import sympy as s
from scipy.integrate import quad
from ksw668_f8_fv_source_flux import exact_cell_averages


def check():
    u=s.symbols('u',positive=True);lap=lambda x:s.diff(x,u,2)+2*s.diff(x,u)/u
    assert [s.expand(s.Rational(2,5)*lap(lap(u**(2*k)))) for k in range(4)]==[0,0,48,336*u*u]
    # Compact smooth radial f and its derivatives have zero endpoint terms,
    # including at u=0 in the weighted radial Green identity.
    target=48*quad(lambda u:u*u*np.exp(1-1/(1-u*u)),0,1,epsabs=1e-13)[0]
    rows=[];eps=.04
    for h in (.008,.006,.004,.003,.002,.001,.0005,.00025,.000125):
        r=np.arange(int(np.ceil(eps/h))+2)*h;u=r/eps;dh=h/eps;l=np.maximum(u-dh/2,0);v=u+dh/2
        x=exact_cell_averages(eps,r,h)[0]
        mom=[float(x@((v**d-l**d)/d)) for d in (3,5,7)]
        node=[float(x@(((v**3-l**3)/3)*u**p)) for p in (0,2,4)]
        rows.append(dict(dr=h,shell_moments=mom,nodal_moments=node,relative_quartic_moment_error=abs(mom[2]-target)/target))
    return dict(continuum_moments=[0,0,target],exact_bilaplacian_test_polynomials=4,rows=rows)

if __name__=='__main__':print(json.dumps(check(),indent=2))
