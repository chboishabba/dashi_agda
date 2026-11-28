"""Native event chart: birth, continued zero-base population, extinction, mixing."""
import numpy as np
from solar_physical_causal import event,MASS,CHARGE
from solar_population_amplitude_event import event_amplitude_jvp,right_reaction_support


def run():
    V=1.; scale=np.sign(CHARGE)*np.sqrt(V*MASS)
    b=np.array([[1.,2.,0.],[3.,-1.,1.],[0.,0.,2.]])
    v=np.array([[2.,-1.,3.],[-2.,1.,0.],[0.,2.,-1.]])
    zero=np.zeros(3); cases=[
        # n,r,a,n_u,r_u,a_u; all events preserve charge.
        (zero,zero,zero,zero,zero,np.array([3.,2.,1.])),
        (zero,zero,zero,np.array([4.,3.,1.]),np.array([2.,1.,1.]),np.array([3.,2.,1.])),
        (np.array([4.,3.,1.]),np.array([4.,3.,1.]),zero,zero,np.array([-2.,-1.,-1.]),np.array([3.,2.,1.])),
        (np.array([4.,4.,0.]),np.array([1.,1.,0.]),np.array([2.,2.,0.]),np.array([1.,0.,1.]),zero,np.array([1.,0.,1.])),
    ]
    errors=[]
    for n,r,a,nu,ru,au in cases:
        z=scale[:,None]*np.sqrt(n)[:,None]*v
        dz=scale[:,None]*np.sqrt(np.where(n==0,nu,0.))[:,None]*v
        dz[n>0]=z[n>0]*.2
        old=(n>0)|(nu>0); new=n-r+a; newu=nu-ru+au
        right=(new>0)|(newu>0)
        primal,t=event_amplitude_jvp(z,n,r,a,b,V,dz,nu,ru,au,old,right)
        assert np.allclose(np.sqrt(n)+t['signed_amplitude_residual'],np.sqrt(new))
        row=[]
        for s in (1e-2,1e-3,1e-4):
            nn=n+s*s*nu; zz=scale[:,None]*np.sqrt(nn)[:,None]*v
            zz[n>0]*=1+s*.2
            out=event(zz,nn,r+s*s*ru,a+s*s*au,b,V)
            fd=(out[0]-primal[0])/s
            row.append(float(np.linalg.norm(fd-t['state_jvp'])/max(np.linalg.norm(t['state_jvp']),1e-20)))
        assert row[-1]<.01,(row,n,r,a)
        errors.append(row)
    q=dict(recombination_m3_s=[1.,1.],ionization_s_inv=[0.,0.],heater_ionization_per_J=[1.,0.])
    right,pool=right_reaction_support([False]*3,[True,False],0.,1.,q)
    assert right.tolist()==[True,True,False]
    # Higher-order support can be true with a zero first amplitude jet.
    _,t=event_amplitude_jvp(np.zeros(9),zero,zero,zero,b,V,np.zeros(9),zero,zero,zero,[False]*3,right)
    assert not np.any(t['amplitude_jvp']) and t['new_right'].any()
    print(dict(status='AMPLITUDE_EVENT_PASS',relative_errors=errors,physical_admission=False))

if __name__=='__main__': run()
