"""One-sided boundary Cayley state derivative across a population support jump.

The padded generator H0 at zero density is NOT the right-side limiting
generator Hplus, because collision and gyro terms switch support. Under
compatibility (Hplus-H0) mid0 = 0 the primal is continuous; the right
state derivative uses the Hplus resolvent, not the H0 resolvent.
A local stage only: new offsite edges require a separate cone schedule.
"""
import numpy as np
from scipy.linalg import solve

def boundary_stage_jvp(Hzero,Hplus,dH,x,dx,force,dt,dforce=None):
    z,p,A=[np.asarray(v,float) for v in (Hzero,Hplus,dH)]
    x=np.asarray(x,float);dx=np.asarray(dx,float);f=np.asarray(force,float)
    df=np.zeros_like(f) if dforce is None else np.asarray(dforce,float)
    d=len(x)
    if dt<=0 or any(M.shape!=(d,d) for M in (z,p,A)):
        raise ValueError('invalid boundary local block')
    if any(v.shape!=(d,) for v in (dx,f,df)):
        raise ValueError('invalid boundary state or force')
    if any(not np.all(np.isfinite(M)) for M in (z,p,A,x,dx,f,df)):
        raise ValueError('nonfinite boundary chart')
    eye=np.eye(d)
    base=solve(eye-dt*z/2,(eye+dt*z/2)@x+dt*f)
    middle=(x+base)/2
    # The full padded limiting operator may jump. The state must not.
    incompat=(p-z)@middle
    if np.linalg.norm(incompat)>1e-10*max(
            1.,np.linalg.norm(z@middle),np.linalg.norm(p@middle)):
        raise ValueError('primal discontinuity at support boundary')
    if np.linalg.eigvalsh(-(p+p.T)/2).min() < -1e-12:
        raise ValueError('nonpassive right-side generator')
    derivative=solve(eye-dt*p/2,
                     (eye+dt*p/2)@dx+dt*(A@middle+df))
    return base,derivative,dict(
        one_sided_amplitude_chart=True,
        generator_continuous=False,
        right_limiting_generator=True,
        new_offsite_stage_admitted=False,
        model_scope='local fixed-face stage; no global zero-support JVP')
