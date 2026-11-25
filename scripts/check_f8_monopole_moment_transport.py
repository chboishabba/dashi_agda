"""Conservative polynomial transfer of the original compact l=0 emitter.
Source-space diagnostics only: extra continuous moments are charged inputs.
No replacement of the original propagation source or receiver claim.
"""
import json
import numpy as np
import sympy as s
from scipy.integrate import quad
from ksw668_f8_fv_source_flux import primitives,exact_cell_averages
from run_f8_monopole_shadow import maps


def check():
    eps=.04;I,_,wc,wf=maps();gc=exact_cell_averages(eps,np.arange(378)*.008,.008)[0,:-1];gf=exact_cell_averages(eps,np.arange(503)*.006,.006)[0,:-1]
    mapped=I@gc;P=primitives()[0]
    p=lambda u:0. if u<=0 or u>=1 else float(P(u))
    h=s.Rational(1,5);hf=s.Rational(3,20);x=s.symbols('x');maxdeg=6
    # Dimensionless source cells, including clipped outer cell; use full target volumes.
    fine=[(max(s.S.Zero,(j-s.Rational(1,2))*hf),(j+s.Rational(1,2))*hf) for j in range(502)]
    result=np.zeros((maxdeg+1,len(fine)));oracle=np.zeros(len(fine));max_moment=0.;max_quad=0.;checks=0
    for j in range(6):
        a=max(s.S.Zero,(j-s.Rational(1,2))*h);b=min(s.S.One,(j+s.Rational(1,2))*h);w=b-a
        lo,hi=float(a),float(b);span=float(w);mom=[p(hi)-p(lo)]
        for k in range(1,maxdeg+1):
            integ,err=quad(lambda u:((u-lo)/span)**(k-1)*p(u),lo,hi,epsabs=1e-10,epsrel=1e-12,limit=150)
            mom.append(p(hi)-k/span*integ);max_quad=max(max_quad,err*k/span)
        # Original whole-cell moment exactly defines the zeroth entry (up to FP).
        assert np.isclose(eps**3*mom[0],wc[j]*gc[j],atol=1e-13,rtol=1e-12)
        G=s.Matrix(maxdeg+1,maxdeg+1,lambda k,l:w*(a*a/s.Integer(k+l+1)+2*a*w/s.Integer(k+l+2)+w*w/s.Integer(k+l+3)))
        # Exact positive Gram for each polynomial degree; exact inverse identity.
        for d in range(maxdeg+1):
            g=G[:d+1,:d+1];gi=g.inv();assert g*gi==s.eye(d+1);assert g.det()>0;checks+=1
            c=np.array(gi,float)@np.array(mom[:d+1]);res=np.max(abs(np.array(g,float)@c-mom[:d+1]));max_moment=max(max_moment,float(res))
            for i,(fa,fb) in enumerate(fine[:9]):
                l,r=max(a,fa),min(b,fb)
                if l>=r:continue
                xl,xr=(l-a)/w,(r-a)/w
                def primitive(z,k):return w*(a*a*z**(k+1)/(k+1)+2*a*w*z**(k+2)/(k+2)+w*w*z**(k+3)/(k+3))
                weights=np.array([float(primitive(xr,k)-primitive(xl,k)) for k in range(d+1)])
                result[d,i]+=eps**3*(weights@c)/wf[i]
                if d==0:oracle[i]+=eps**3*(p(float(r))-p(float(l)))/wf[i]
    norm=lambda a:float(np.sqrt(wf@(a*a)))
    base=norm(mapped-gf)/norm(gf)
    rows=[dict(degree=d,relative=norm(r-gf)/norm(gf),weighted_moment=float(wf@r),max_abs=float(np.max(abs(r-gf)))) for d,r in enumerate(result)]
    assert norm(oracle-gf)/norm(gf)<1e-12
    assert max(abs(wf@r-wc@gc) for r in result)<1e-8
    return dict(base_relative=base,rows=rows,oracle_relative=norm(oracle-gf)/norm(gf),exact_gram_checks=checks,max_moment_residual=max_moment,max_quad_estimate=max_quad,source_cells=6,coarse_moment=float(wc@gc),fine_moment=float(wf@gf),fine_outer_cells=gf[5:7].tolist(),reconstructed_outer_cells=result[:,5:7].tolist())

if __name__=='__main__':print(json.dumps(check(),indent=2))
