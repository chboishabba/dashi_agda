"""Original compact TT monopole: physical shell projection resolution audit.
Not a Fourier cutoff, propagated Weyl estimate, or interval-certified norm.
"""
import json
import numpy as np
import sympy as s
from scipy.integrate import quad
from numpy.polynomial.legendre import leggauss
from ksw668_f8_fv_source_flux import exact_cell_averages


def check():
    u=s.symbols('u',positive=True);f=s.Function('f')(u)
    primitive=lambda f:s.Rational(2,5)*(u*u*s.diff(f,u,3)+2*u*s.diff(f,u,2)-2*s.diff(f,u))
    lap=lambda f:s.diff(f,u,2)+2*s.diff(f,u)/u
    assert s.expand(s.diff(primitive(f),u)/u**2-s.Rational(2,5)*lap(lap(f)))==0
    f=s.exp(1-1/(1-u*u));g=s.diff(primitive(f),u)/u**2
    fun=s.lambdify(u,g,'numpy');eps=.04
    z,e=quad(lambda u:u*u*fun(u)**2,0,1,epsabs=1e-9,epsrel=1e-11,limit=200)
    norm=eps**3*z;cross=[]
    for n in (256,512):
        x,w=leggauss(n);x=(x+1)/2
        cross.append(float(eps**3*np.sum(w*x*x*fun(x)**2)/2))
    assert max(abs(a-norm) for a in cross)<1e-8*norm
    rows=[]
    for h in (.008,.006,.004,.003,.002,.001,.0005,.00025,.000125):
        r=np.arange(int(np.ceil(eps/h))+2)*h;v=((r+h/2)**3-np.maximum(r-h/2,0)**3)/3
        x=exact_cell_averages(eps,r,h)[0];captured=float(v@(x*x)/norm)
        assert 0<=captured<=1
        rows.append(dict(dr=h,cells=int(np.count_nonzero(x)),captured_squared_norm=captured,relative_projection_error=float(np.sqrt(1-captured)),weighted_moment=float(v@x)))
    return dict(exact_bilaplacian_identity=True,continuous_squared_norm=float(norm),quad_error_estimate=float(eps**3*e),gauss_crosscheck=cross,rows=rows)

if __name__=='__main__':print(json.dumps(check(),indent=2))
