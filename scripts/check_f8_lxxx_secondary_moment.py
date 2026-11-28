"""LXXX: same native FV source, corrected within-cell second moments.
Retain primitive owner; cell-centre substitution is a negative control.
Numerical quadrature is not a certified rational interval proof.
"""
import numpy as np
from scipy.integrate import quad
from ksw668_f8_fv_source_flux import primitives, exact_cell_averages

def test():
    eps=.04;p2=primitives()[1]
    def p(u):return 0. if u in (0.,1.) else float(p2(u))
    for dr in (.008,.004,.002,.001):
        r=np.arange(round(.096/dr)+1)*dr
        src=exact_cell_averages(eps,r,dr)
        def vol(d):
            return ((r+dr/2)**d-np.maximum(0,r-dr/2)**d)/d
        b2=src[1]*vol(7)/eps**7
        b4=src[2]*vol(11)/eps**11
        m2=[]
        for x in r:
            a=max(0,(x-dr/2)/eps);b=min(1,(x+dr/2)/eps)
            if b<=a:m2.append(0.);continue
            integration=quad(lambda u:2*u*p(u),a,b,epsabs=5e-12,epsrel=1e-12,limit=150)[0]
            m2.append(b*b*p(b)-a*a*p(a)-integration)
        centre=9*np.sum((r/eps)**2*b2)-40*np.sum(b4)
        corrected=9*sum(m2)-40*np.sum(b4)
        assert abs(corrected)<1e-8, (dr,corrected)
        assert abs(centre)>1e-2, (dr,centre)
        print(f"PASS dr={dr:g}: centroid defect={centre:.12g}, "
              f"exact-moment quadrature defect={corrected:.12g}",flush=True)

if __name__=="__main__":test()
