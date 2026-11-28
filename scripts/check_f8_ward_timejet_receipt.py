"""F8 W1/W2 source-time-jet numerical producer and negative controls.

Differentiates the EXISTING History.known_ward tensor/Israel/Ward output
in time, not an invented source. A five-point pair and h/2 refinement
measures a defect, NOT a certified interval enclosure. Optional actual
history requires all original donor scripts and is not run by default.
"""
import argparse
import numpy as np


def jets(eval_at, t, h):
    """Return original value, first, second time jets, and refinement defects."""
    if h<=0:raise ValueError('positive h required')
    def sample(step):
        y=[tuple(np.asarray(z,complex) for z in eval_at(t+i*step))
           for i in (-2,-1,0,1,2)]
        if len(set(len(row) for row in y))!=1:raise ValueError('source tuple mismatch')
        if any(z.shape!=y[2][j].shape for row in y for j,z in enumerate(row)):
            raise ValueError('source tensor shape mismatch')
        d1=tuple((a-8*b+8*d-e)/(12*step) for a,b,c,d,e in zip(*y))
        d2=tuple((-a+16*b-30*c+16*d-e)/(12*step**2)
                 for a,b,c,d,e in zip(*y))
        return y[2],d1,d2
    val,a,b=sample(h); _,ar,br=sample(h/2)
    assert all(np.all(np.isfinite(z)) for row in (val,ar,br) for z in row)
    err1=max(np.max(np.abs(x-y)) for x,y in zip(a,ar))
    err2=max(np.max(np.abs(x-y)) for x,y in zip(b,br))
    return {'value':val,'dt':ar,'dtt':br,'defect_dt':float(err1),
            'defect_dtt':float(err2)}


def synthetic():
    # Analytic time jets of nontrivial full tensor + Ward current, including
    # oscillatory complex Fourier symmetry. This is not original history.
    t=.85;h=1/128
    def output(x):
        f=np.exp(1j*2*x)*(1+x+x*x)
        T=np.array([[f,0],[0,3*f]],complex)
        C=np.array([[f*x,0],[0,-2*f]],complex)
        R=np.array([x*f,f.conjugate()],complex)
        return T,C,R
    got=jets(output,t,h)
    for j in range(3):
        eps=1e-6
        ref=(np.array(output(t+eps)[j])-np.array(output(t-eps)[j]))/(2*eps)
        assert np.max(abs(got['dt'][j]-ref))<1e-7
    assert got['defect_dt']<1e-7
    assert got['defect_dtt']<1e-6
    # A physically smooth source can still give an uncaught midpoint error
    # if no independent interval/regularity bound is supplied.
    p=np.poly1d([1,0,-5*h*h,0,4*h**4,0])
    assert all(abs(p(v))<1e-10 for v in (-2*h,-h,0,h,2*h))
    assert abs(np.polyder(p)(h/3))>0
    print('PASS synthetic full tensor+Ward time jets, two-stencil defects, undetected-polynomial negative control')


def original(K=10,cells=64,nh=8,nodes=3,h=1e-3):
    from check_f8_full_band_wall_controller import History
    from check_f8_material_clock_controller import source_shear_bound
    HH=History(K=K,cells=cells,nh=nh,nodes=nodes,end=1.055)
    muS=source_shear_bound()+1
    for k in (0.,K/2,3*K/2,5*K/2,3*K):
        result=jets(lambda t:HH.known_ward(t,k,muS=muS),1.035,h)
        if k>=3*K:
            assert all(np.max(abs(z))<1e-12 for row in ('value','dt','dtt') for z in result[row])
        print('ORIGINAL wall timejets',k,result['defect_dt'],result['defect_dtt'],flush=True)
    print('ORIGINAL finite time-jets calculated; defects are NOT certified enclosures')


if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('--original',action='store_true')
    args=ap.parse_args()
    synthetic()
    if args.original:original()
