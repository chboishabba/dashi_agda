"""Directional derivatives of original spherical reaction and thermal maps.
Positive support chart only; zero support is handled separately, never divided by.
"""
import numpy as np
from solar_physical_causal import reaction,event,MASS,CHARGE

def reaction_jvp(n,pool,T,p,h,q,dn,dpool,dT,dp):
    alpha=np.asarray(q['recombination_m3_s']); k=np.asarray(q['ionization_s_inv'])
    g=np.asarray(q['heater_ionization_per_J']); Q=np.asarray(q.get('activation_temperature_K',[0.,0.]))
    exp=np.exp(-h*alpha*n[0]); r=n[1:]*(1-exp)
    dr=dn[1:]*(1-exp)+n[1:]*exp*h*alpha*dn[0]
    avail=pool+r; davail=dpool+dr
    rate=k*np.exp(-Q/T)+g*p; drate=k*np.exp(-Q/T)*Q*dT/T**2+g*dp
    surv=np.exp(-h*rate); a=avail*(1-surv)
    da=davail*(1-surv)+avail*surv*h*drate
    primal=reaction(n,pool,T,p,h,q)
    assert np.allclose(primal[0],np.r_[r.sum(),r]) and np.allclose(primal[1],np.r_[a.sum(),a])
    return primal,(np.r_[dr.sum(),dr],np.r_[da.sum(),da],davail-da)

def thermal_jvp(theta,p,h,cap,cool,dtheta,dp):
    a=np.exp(-h*cool/cap); beta=-np.expm1(-h*cool/cap)/cool
    return a*theta+beta*p,a*dtheta+beta*dp

def event_jvp(z,n,r,a,b,V,dz,dn,dr,da):
    """Fixed birth velocity; strictly positive old/new population branch."""
    z=np.asarray(z).reshape(3,3); dz=np.asarray(dz).reshape(3,3)
    remain=n-r; dremain=dn-dr; new=remain+a; dnew=dremain+da
    assert np.all(n>0) and np.all(new>0)
    coeff=remain/np.sqrt(n*new)
    dc=dremain/np.sqrt(n*new)-coeff*(dn/n+dnew/new)/2
    scale=np.sign(CHARGE)*np.sqrt(V*MASS/new)
    out=coeff[:,None]*z+(scale*a)[:,None]*b
    dout=coeff[:,None]*dz+dc[:,None]*z+(scale*(da-a*dnew/(2*new)))[:,None]*b
    primal=event(z,n,r,a,b,V)
    assert np.allclose(primal[0],out.ravel())
    return primal,(dout.ravel(),dnew)

def collision_jvp(rows,neutral,dT):
    from solar_earth_collision_tensor import rates
    T=np.array([r['te'] for r in rows]); O,N2,O2=neutral[:,1],neutral[:,2],neutral[:,3]
    dve=2.33e-17*N2*(1-2*1.21e-4*T)+1.82e-16*O2*(.5/np.sqrt(T)+.036)+8.9e-17*O*(.5/np.sqrt(T)+1.5*5.7e-4*np.sqrt(T))
    return rates(rows,neutral),np.column_stack((dve*dT,np.zeros_like(T),np.zeros_like(T)))
