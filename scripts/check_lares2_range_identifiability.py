#!/usr/bin/env python3
"""Synthetic LARES-class rotating-station range and KK-signature identifiability.
Not actual SLR, no two-way photon light-time, Earth multipoles or source matching.
"""
import numpy as np
from scipy.constants import G,c
MU=3.986004418e14; RE=6378137.; J=5.86e33
YEAR=365.256363004*86400.; SIDEREAL=86164.0905
def orbit(t,rate,a=12270e3):
    phase=np.sqrt(MU/a**3)*t+.2; node=.38+rate*t; inc=1.25
    x=a*np.cos(phase);y=a*np.cos(inc)*np.sin(phase);z=a*np.sin(inc)*np.sin(phase)
    return np.stack([np.cos(node)*x-np.sin(node)*y,np.sin(node)*x+np.cos(node)*y,z],axis=-1)
def station(t):
    th=.2+2*np.pi*t/SIDEREAL;lat=.57
    return np.stack([RE*np.cos(lat)*np.cos(th),RE*np.cos(lat)*np.sin(th),np.full_like(t,RE*np.sin(lat))],axis=-1)
def rng(t,rate):return np.linalg.norm(orbit(t,rate)-station(t),axis=1)
def project(signal,K,sigma):
    X=K/sigma[:,None];y=signal/sigma
    U,sv,_=np.linalg.svd(X,full_matrices=False)
    rank=sum(sv>sv[0]*1e-10)
    return y-U[:,:rank]@(U[:,:rank].T@y),rank
def main():
    t=np.linspace(0,.75*YEAR,600)
    rate=2*G*J/(c*c*(12270e3)**3);h=1e-3
    signal=(rng(t,rate*(1+h))-rng(t,rate*(1-h)))/(2*h)
    K=np.stack([np.ones_like(t),t/YEAR,np.sin(2*np.pi*t/SIDEREAL)],axis=-1)
    sigma=np.full(t.size,.01)
    residual,rank=project(signal,K,sigma); info=residual@residual
    assert rank==3 and info>0
    collision,_=project(signal,np.column_stack([K,signal]),sigma)
    assert np.linalg.norm(collision)<1e-6*np.linalg.norm(signal/sigma)
    delta=-2*(MU/c**2)*np.sinh(1.)**2/12270e3
    print('GR nodal mas/year:',rate*YEAR*(180/np.pi)*3600000)
    print('Synthetic nuisance-marginalized sigma_delta:',info**(-.5))
    print('KK proxy delta:',delta,'synthetic significance:',abs(delta)*np.sqrt(info))
    print('PASS common range operator, nuisance projection and nonidentifiability witness')
    print('NO real SLR, laser light-time or physical KK Earth inference')
if __name__=='__main__':main()
