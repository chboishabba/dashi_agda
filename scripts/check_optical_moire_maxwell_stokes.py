#!/usr/bin/env python3
"""Synthetic optical moire Maxwell/Stokes benchmark; not experimental replay.
Constructs three rotated transverse plane-wave harmonics per layer and
propagates by source-free angular spectrum, recovering longitudinal E.
"""
import argparse, json
import numpy as np

def grid(n,L):
    v=(np.arange(n)-n//2)*L/n
    x,y=np.meshgrid(v,v)
    k=2*np.pi*np.fft.fftfreq(n,L/n)
    kx,ky=np.meshgrid(k,k)
    return x,y,kx,ky

def layer(x,y,k,theta,hand):
    c,s=np.cos(theta),np.sin(theta)
    u,v=c*x+s*y,-s*x+c*y
    ph=[k*(np.cos(t)*u+np.sin(t)*v) for t in (0,2*np.pi/3,4*np.pi/3)]
    a=sum(np.exp(1j*(p+i*2*np.pi/3)) for i,p in enumerate(ph))/3
    b=sum(np.exp(1j*(p-i*2*np.pi/3)) for i,p in enumerate(ph))/3
    return np.stack([a,1j*hand*b])

def propagate(e,L,k0,z):
    _,_,kx,ky=grid(e.shape[-1],L)
    kz=np.sqrt(np.maximum(0,k0*k0-kx*kx-ky*ky))
    inside=kz>0
    f=np.fft.fft2(e,axes=(-2,-1))*inside*np.exp(1j*kz*z)
    zz=np.zeros_like(f[0])
    np.divide(-(kx*f[0]+ky*f[1]),kz,out=zz,where=inside)
    full=np.concatenate((f,zz[None]))
    err=np.max(np.abs(kx*full[0]+ky*full[1]+kz*full[2]))/(k0*max(1,np.max(np.abs(full))))
    return np.fft.ifft2(full,axes=(-2,-1)),float(err)

def stokes(f,floor=1e-12):
    x,y=f[:2]
    power=np.abs(x)**2+np.abs(y)**2
    valid=power>floor
    q=np.stack([2*np.real(np.conj(x)*y),2*np.imag(np.conj(x)*y),np.abs(x)**2-np.abs(y)**2])
    s=np.full(q.shape,np.nan)
    np.divide(q,power,out=s,where=valid)
    return s,valid,power

def omega(a,b,c):
    p=np.einsum('i...,i...->...',a,np.cross(b,c,axisa=0,axisb=0,axisc=0))
    d=1+np.einsum('i...,i...->...',a,b)+np.einsum('i...,i...->...',b,c)+np.einsum('i...,i...->...',c,a)
    return 2*np.arctan2(p,d)

def patch_charge(s,valid):
    if not valid.all(): return None # fail closed at polarization singularity
    a,b,c,d=s[:,:-1,:-1],s[:,:-1,1:],s[:,1:,1:],s[:,1:,:-1]
    return float(np.sum(omega(a,b,c)+omega(a,c,d))/(4*np.pi))

def run(n=128,L=20.,k=3.,wavelength=1.,angle=13.2,z=0.,obstruct=False):
    x,y,_,_=grid(n,L)
    e=layer(x,y,k,0,1)+layer(x,y,k,np.deg2rad(angle),-1)
    if obstruct: e=e*(x*x+y*y>(.1*L)**2)
    f,residual=propagate(e,L,2*np.pi/wavelength,z)
    s,valid,power=stokes(f)
    return dict(angle_deg=angle,z=z,obstruction=obstruct,
                maxwell_divergence_relative=residual,
                intensity_sum=float(power.sum()),
                nonzero_intensity_fraction=float(valid.mean()),
                open_patch_integral_not_integer_degree=patch_charge(s,valid))

def test():
    p=run(n=64)
    assert p['maxwell_divergence_relative']<1e-12,p
    v=np.ones((3,3),complex)
    s,good,_=stokes(np.stack([v,1j*v]))
    assert good.all() and np.allclose(s[1],1)
    assert abs(patch_charge(s,good))<1e-12
    _,good,_=stokes(np.zeros((2,3,3),complex))
    assert not good.any()
    return p

if __name__=='__main__':
    q=argparse.ArgumentParser()
    q.add_argument('--test',action='store_true')
    q.add_argument('--angle',type=float,default=13.2)
    q.add_argument('--z',type=float,default=0.)
    q.add_argument('--n',type=int,default=128)
    q.add_argument('--obstruct',action='store_true')
    a=q.parse_args()
    print(json.dumps(test() if a.test else run(n=a.n,angle=a.angle,z=a.z,obstruct=a.obstruct),indent=2))
