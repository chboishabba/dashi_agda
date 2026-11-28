"""Native mode-3 radial-source VJP through original SSPRK3.

Reuses the existing stage and warp_stage_adjoint.transpose. The finite
5-step regression observes the corrected full-spatial Delta3 component,
NOT the complete E4/E5 temporal Weyl observer or physical 12-unit run.
The exact rational dual treats computed float sensitivity as literal input:
it does not bound floating adjoint or time-integration error.
"""
from fractions import Fraction as Q
from math import ceil
import numpy as np
from ksw668_f8_tt_multipole import stage
from warp_stage_adjoint import transpose
from check_f8_lxxv_taylor import enclose
from check_f8_lxxviii_joint_moments import box_error, dual_upper, exact_witness
from ksw668_f8_weak_source import weak_source


def cp_cm(nr):
    cp=np.zeros((3,nr));cm=np.zeros((3,nr))
    for q in range(3):
        d=3+4*q
        for j in range(1,nr):
            den=(j+.5)**d-(j-.5)**d
            cp[q,j]=d*(j+.5)**(d-1)/den
            cm[q,j]=d*(j-.5)**(d-1)/den
    return cp,cm


def stage_step(x,src,z,h,dr,dy,cp,cm):
    b,v,amp=z
    out=np.zeros_like(x)
    stage(*x,*out,dr,dy,b,v,amp,src,cp,cm,3)
    return x+h*out


def adj_step(x,z,h,dr,dy):
    b,v,_=z
    return x+h*transpose(x,dr,dy,b,v,3)


def source_vjp(obs,clock,h,dr,dy):
    """Exact discrete SSPRK3 reverse formula with native source Jacobian.

    The only mode-3 source dependence in the non-affine stage is
    d(Mdot[q,0,i])/d(src[q,i]) = -4*amp/dy. No physical C3 mode symmetry.
    """
    lam=obs.copy();k=np.zeros((3,obs.shape[-1]))
    for a0,a1,ah in reversed(clock):
        k+=(-4*ah[2]/dy)*(2*h/3)*lam[2,:,0,:]
        l2=(2/3)*adj_step(lam,ah,h,dr,dy)
        k+=(-4*a1[2]/dy)*(h/4)*l2[2,:,0,:]
        l1=.25*adj_step(l2,a1,h,dr,dy)
        k+=(-4*a0[2]/dy)*h*l1[2,:,0,:]
        lam=lam/3+.75*l2+adj_step(l1,a0,h,dr,dy)
    k[:,-1]=0
    return k


def forward(src,obs,clock,h,dr,dy,cp,cm):
    x=np.zeros_like(obs)
    for a0,a1,ah in clock:
        x1=stage_step(x,src,a0,h,dr,dy,cp,cm)
        x2=.75*x+.25*stage_step(x1,src,a1,h,dr,dy,cp,cm)
        x=x/3+(2/3)*stage_step(x2,src,ah,h,dr,dy,cp,cm)
    return float(np.vdot(obs,x))


def spatial_covector(dr,eps,nr):
    obs=np.zeros((3,3,6,nr))
    ir=4;r=ir*dr
    for q in range(3):
        ell=2*q;fac=(r/eps)**ell
        obs[0,q,0,ir-1:ir+2]+=fac*np.array([
            1/dr**2-(2*ell+2)/(2*dr*r), -2/dr**2,
            1/dr**2+(2*ell+2)/(2*dr*r)])
    return obs


def run(h):
    dr=float(h)*.04;dy=.012;dt=.00018;eps=.04
    n=ceil(1/h)+1;nr=max(n+1,9)
    cp,cm=cp_cm(nr)
    clock=[((.48,-.35,a),(.477,-.353,a*1.15),(.479,-.352,a*.92))
           for a in (-.08,-.15,-.2,-.12,-.04)]
    obs=spatial_covector(dr,eps,nr)
    k=source_vjp(obs,clock,dt,dr,dy)
    rng=np.random.default_rng(1527)
    src=rng.normal(size=(3,nr));src[:,-1]=0
    actual=forward(src,obs,clock,dt,dr,dy,cp,cm)
    predicted=float(np.vdot(k,src))
    np.testing.assert_allclose(actual,predicted,rtol=1e-10,atol=1e-11)
    source=weak_source(eps,np.arange(n+1)*dr,dr)
    lower,upper,rows,defect=box_error(enclose(h,20),source,h)
    witness,piv=exact_witness(lower,upper,rows,defect,h)
    assert witness is not None
    assert all(a<=x<=b for x,a,b in zip(witness,lower,upper))
    c=[]
    for q in range(3):
        d=3+4*q
        for i in range(n):
            w=((i*h+h/2)**d-max(Q(0),i*h-h/2)**d)/d
            c.append(Q(float(k[q,i]))/w)
    zeros=[Q(0)]*4
    def enclosure(lam):
        hi=dual_upper(c,lower,upper,rows,defect,defect,lam)
        lo=-dual_upper([-x for x in c],lower,upper,rows,defect,defect,[-x for x in lam])
        return lo,hi
    box=enclosure(zeros)
    A=np.array([[float(a) for a in row] for row in rows])
    cf=np.array([float(x) for x in c])
    fit=np.linalg.lstsq(A.T,cf,rcond=None)[0]
    candidate=enclosure([Q(float(v)).limit_denominator(10**8) for v in fit])
    value=sum((a*b for a,b in zip(c,witness)),Q(0))
    assert box[0]<=value<=box[1]
    assert candidate[0]<=value<=candidate[1]
    chosen=max(box[0],candidate[0]),min(box[1],candidate[1])
    assert chosen[0]<=value<=chosen[1]
    result=dict(mesh=str(h),steps=len(clock),modes=3,
                source_vjp_abs_discrepancy=abs(actual-predicted),
                witness_defect=float(value),box=[float(z) for z in box],
                projected=[float(z) for z in candidate],
                selected=[float(z) for z in chosen],pivots=piv)
    print(result,flush=True)
    return result


if __name__=='__main__':
    for h in (Q(1,5),Q(3,20)):
        run(h)
