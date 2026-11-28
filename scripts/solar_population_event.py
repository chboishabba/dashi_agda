"""Original population event and reaction, independent of data/port imports."""
import numpy as np
from scipy.constants import elementary_charge as e, electron_mass as me, atomic_mass as u

MASS=np.array([me,30.5*u,16*u])
CHARGE=e*np.array([-1.,1.,1.])

def event(z,n,removed,created,birth,volume):
    """Fixed padded chart, exact zero support, arbitrary birth velocities."""
    z=np.asarray(z,float).reshape(3,3); n=np.asarray(n,float)
    r=np.asarray(removed,float); c=np.asarray(created,float); b=np.asarray(birth,float)
    assert np.all(n>=0) and np.all(r>=0) and np.all(r<=n) and np.all(c>=0)
    assert abs((c-r)@CHARGE)<=1e-12*((c+r)@abs(CHARGE))
    w=volume*MASS
    scale=np.sqrt(w*n)
    assert np.all(z[n==0]==0)
    v=np.divide(np.sign(CHARGE)[:,None]*z,scale[:,None],out=np.zeros_like(z),where=scale[:,None]>0)
    a=n-r; new=a+c
    momentum=a[:,None]*v+c[:,None]*b
    vv=np.divide(momentum,new[:,None],out=np.zeros_like(v),where=new[:,None]>0)
    out=np.sign(CHARGE)[:,None]*np.sqrt(w*new)[:,None]*vv
    incoming=.5*np.sum(w*c*np.sum(b*b,axis=1))
    outgoing=.5*np.sum(w*r*np.sum(v*v,axis=1))
    mix=.5*np.sum(w*np.divide(a*c,new,out=np.zeros_like(new),where=new>0)*np.sum((v-b)**2,axis=1))
    residual=(np.sum(out*out)-np.sum(z*z))/2-incoming+outgoing+mix
    assert abs(residual)<=1e-10*max(incoming,outgoing,mix,np.sum(z*z),1e-30)
    return out.ravel(),new,np.array([incoming,outgoing,mix])

def reaction(n,neutral,temperature,power,dt,q):
    """Two charge-neutral ionization/recombination channels.
    Explicit nonnegative rate parameters; donor reservoir tracks ion counts.
    No rate coefficients inferred from radar density differences.
    """
    alpha=np.asarray(q['recombination_m3_s'],float)
    k=np.asarray(q['ionization_s_inv'],float)
    activation=np.asarray(q['heater_ionization_per_J'],float)
    threshold=np.asarray(q.get('activation_temperature_K',[0.,0.]),float)
    assert threshold.shape==(2,) and np.all(threshold>=0) and temperature>0
    assert alpha.shape==k.shape==activation.shape==(2,)
    assert np.all(alpha>=0) and np.all(k>=0) and np.all(activation>=0)
    neutral=np.asarray(neutral,float)
    # First recombine, then ionize available neutral precursor; both pairwise.
    r=n[1:]*(-np.expm1(-dt*alpha*n[0]))
    pool=neutral+r
    c=pool*(-np.expm1(-dt*(k*np.exp(-threshold/temperature)+activation*power)))
    return np.r_[r.sum(),r],np.r_[c.sum(),c],pool-c
