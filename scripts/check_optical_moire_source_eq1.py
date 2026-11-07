#!/usr/bin/env python3
"""Attributed Dev--Shen (2026) Eq. (1) Gaussian Fourier-source replay.
Source: DOI 10.1038/s41377-026-02533-w.
Original result and experimental authority: Vasu Dev and Yijie Shen.
DASHI owns only this implementation and synthetic numerical tests.
Selected dimensionless parameters are NOT measured paper parameters.
"""
import argparse, json
import numpy as np

SOURCE={"authors":"Vasu Dev and Yijie Shen","doi":"10.1038/s41377-026-02533-w",
        "relationship":"published Eq(1) source; no transfer of empirical authority"}

def ring(n,N=6,m=1,radius=11.,waist=2.,ratio=1.,phase=0.,theta=0.):
    if N not in (3,4,6) or n<16 or radius<=0 or waist<=0:
        raise ValueError("invalid selected synthetic ring parameters")
    freq=np.fft.fftshift(np.fft.fftfreq(n))*n
    x,y=np.meshgrid(freq,freq)
    R=np.zeros((n,n),complex); L=np.zeros_like(R)
    for j in range(1,N+1):
        d=np.pi*(2*j-1)/N+theta
        beam=np.exp(-((x-radius*np.cos(d))**2+(y-radius*np.sin(d))**2)/waist**2)
        R+=beam
        L+=ratio*beam*np.exp(1j*(phase+m*2*np.pi*(j-1)/N))
    return np.stack((R,L))

def cartesian(circular):
    R,L=circular
    return np.stack(((R+L)/np.sqrt(2),1j*(L-R)/np.sqrt(2)))

def maxwell(spec,k0=2*np.pi,z=0.,dx=1.):
    n=spec.shape[-1]
    k=2*np.pi*np.fft.fftshift(np.fft.fftfreq(n,d=dx))
    kx,ky=np.meshgrid(k,k); k2=kx*kx+ky*ky
    kz=np.sqrt(np.maximum(k0*k0-k2,0))
    good=k2<k0*k0
    f=spec*good[None]*np.exp(1j*kz*z)[None]
    ez=np.zeros_like(f[0])
    np.divide(-kx*f[0]-ky*f[1],kz,out=ez,where=good)
    rel=np.max(np.abs(kx*f[0]+ky*f[1]+kz*ez))/(k0*max(np.max(np.abs(f)),1e-30))
    full=np.concatenate((f,ez[None]))
    return np.fft.ifft2(np.fft.ifftshift(full,axes=(-2,-1)),axes=(-2,-1)),float(rel)

def stokes(field):
    x,y=field[:2]
    p=np.abs(x)**2+np.abs(y)**2
    valid=p>1e-14*np.max(p) if np.max(p)>0 else np.zeros_like(p,dtype=bool)
    v=np.stack((2*np.real(np.conj(x)*y),2*np.imag(np.conj(x)*y),np.abs(x)**2-np.abs(y)**2))
    out=np.full(v.shape,np.nan)
    np.divide(v,p,out=out,where=valid)
    return out,valid,p

def solid_angle(a,b,c):
    numer=np.sum(a*np.cross(b,c,axis=0),axis=0)
    denom=1+np.sum(a*b+b*c+c*a,axis=0)
    return 2*np.arctan2(numer,denom)

def patch_charge(s,valid):
    if not np.all(valid): return None
    a,b,c,d=s[:,:-1,:-1],s[:,:-1,1:],s[:,1:,1:],s[:,1:,:-1]
    return float(np.sum(solid_angle(a,b,c)+solid_angle(a,c,d))/(4*np.pi))

def run(n=128,N=6,angle=13.2,z=0.,obstacle=0.):
    left=ring(n,N)
    right=ring(n,N,theta=np.deg2rad(angle))
    spec=cartesian(left+right)
    if obstacle>0:
        initial,_=maxwell(spec)
        yi,xi=np.indices((n,n))
        mask=(xi-n/2)**2+(yi-n/2)**2>(obstacle*n)**2
        spec=np.fft.fftshift(np.fft.fft2(initial[:2]*mask[None],axes=(-2,-1)),axes=(-2,-1))
    field,res=maxwell(spec,z=z)
    s,valid,p=stokes(field)
    return {"source":SOURCE,"status":"synthetic source-equation computational replay, NOT experimental reproduction",
            "symmetry":N,"twist_angle_deg":angle,"z":z,
            "maxwell_transversality_relative":res,"valid_stokes_fraction":float(np.mean(valid)),
            "intensity_sum":float(np.sum(p)),
            "open_patch_integral_not_integer_degree":patch_charge(s,valid)}

def test():
    for N in (3,4,6):
        assert np.linalg.norm(ring(128,N))>0
    assert np.linalg.norm(ring(128,m=0)-ring(128,m=1))>1e-5
    assert np.linalg.norm(ring(128,theta=.2)-ring(128,theta=0))>1e-5
    f=cartesian(ring(128))
    a,e0=maxwell(f,z=0)
    b,e1=maxwell(f,z=.5)
    assert max(e0,e1)<1e-12 and abs(np.linalg.norm(a)-np.linalg.norm(b))<1e-10
    ones=np.ones((7,7),complex)
    s,valid,_=stokes(np.stack((ones,1j*ones)))
    assert abs(patch_charge(s,valid))<1e-12
    s,valid,_=stokes(np.zeros((2,7,7),complex))
    assert patch_charge(s,valid) is None
    # Belavin-Polyakov stereographic unit texture: finite OPEN window.
    # It approaches degree -1 with increasing domain radius, while being
    # noninteger for any selected finite rectangular window.
    q=[]
    for radius in (6.,12.):
        coord=np.linspace(-radius,radius,101)
        xx,yy=np.meshgrid(coord,coord)
        rr=xx*xx+yy*yy
        bp=np.stack((2*xx/(1+rr),2*yy/(1+rr),(rr-1)/(1+rr)))
        q.append(patch_charge(bp,np.ones((101,101),bool)))
    assert q[0]<-.95 and q[1]<-.99 and abs(q[1]+1)<abs(q[0]+1)
    return {"synthetic_regression":"PASS","source_doi":SOURCE["doi"],
            "maxwell_residual":max(e0,e1),"norm_delta":float(abs(np.linalg.norm(a)-np.linalg.norm(b))),
            "tested_symmetries":[3,4,6], "finite_window_BP_charges":q}

if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("--test",action="store_true")
    p.add_argument("--size",type=int,default=128)
    p.add_argument("--symmetry",type=int,default=6)
    p.add_argument("--angle",type=float,default=13.2)
    p.add_argument("--z",type=float,default=0.)
    p.add_argument("--obstacle",type=float,default=0.)
    a=p.parse_args()
    print(json.dumps(test() if a.test else run(a.size,a.symmetry,a.angle,a.z,a.obstacle),indent=2))
