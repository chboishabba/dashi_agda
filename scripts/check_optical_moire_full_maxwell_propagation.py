#!/usr/bin/env python3
"""Independent vacuum Maxwell and propagation consumer for Dev & Shen (2026).

Original authors of optical moire supertopologies, Eq. (1), and experiments:
Vasu Dev and Yijie Shen, DOI 10.1038/s41377-026-02533-w.
Published 690-file dataset: DOI 10.21979/N9/AJB6FD, CC BY-NC 4.0.

DASHI's selected dimensions, wavelength, simulation parameters and tests
are numerical demonstrations, NOT reconstruction of measured apparatus
parameters or original experimental evidence. No source is a theorem.
"""
import argparse
import json
import numpy as np
from scipy.constants import c
from check_optical_moire_source_eq1 import ring, cartesian, stokes

SOURCE={"original_authors":"Vasu Dev; Yijie Shen",
        "article_doi":"10.1038/s41377-026-02533-w",
        "dataset_doi":"10.21979/N9/AJB6FD",
        "status":"selected-parameter synthetic forward model, not source-data reproduction"}

def forward(spec,z=0.,window=.003,wavelength=532e-9):
    n=spec.shape[-1]
    k0=2*np.pi/wavelength
    omega=c*k0
    k=2*np.pi*np.fft.fftshift(np.fft.fftfreq(n,d=window/n))
    kx,ky=np.meshgrid(k,k)
    sq=kx*kx+ky*ky
    inside=sq<k0*k0
    kz=np.sqrt(np.maximum(k0*k0-sq,0.))
    et=spec*inside[None]*np.exp(1j*kz*z)[None]
    ez=np.zeros_like(et[0])
    np.divide(-(kx*et[0]+ky*et[1]),kz,out=ez,where=inside)
    E=np.concatenate((et,ez[None]))
    K=np.stack((kx,ky,kz))
    B=np.cross(K,E,axisa=0,axisb=0,axisc=0)/omega
    norm=max(np.linalg.norm(E),1e-30)
    residual={
      "divE":float(np.linalg.norm(np.sum(K*E,axis=0))/(k0*norm)),
      "divB":float(np.linalg.norm(np.sum(K*B,axis=0))/(k0*max(np.linalg.norm(B),1e-30))),
      "Faraday":float(np.linalg.norm(np.cross(K,E,axisa=0,axisb=0,axisc=0)-omega*B)/(k0*norm)),
      "Ampere":float(np.linalg.norm(np.cross(K,B,axisa=0,axisb=0,axisc=0)+omega/c**2*E)/(k0*norm/c))}
    field=np.fft.ifft2(np.fft.ifftshift(E,axes=(-2,-1)),axes=(-2,-1))
    return field,residual

def source_spectrum(n=128,N=6,angle=13.2,waist=1.2):
    first=ring(n,N=N,waist=waist)
    second=ring(n,N=N,waist=waist,theta=np.deg2rad(angle))
    return cartesian(first+second)

def case(n=128,N=6,angle=13.2,z=.5,obstacle=.07):
    spec=source_spectrum(n,N,angle)
    first,r0=forward(spec,z=0.)
    target,rt=forward(spec,z=z)
    y,x=np.indices((n,n))
    disk=(x-n/2)**2+(y-n/2)**2<(obstacle*n)**2
    blocked=first[:2]*(~disk)[None]
    propagated_spectrum=np.fft.fftshift(np.fft.fft2(blocked,axes=(-2,-1)),axes=(-2,-1))
    restored,rb=forward(propagated_spectrum,z=z)
    ref=target[:2][:,disk]
    actual=restored[:2][:,disk]
    err=np.linalg.norm(actual-ref)/max(np.linalg.norm(ref),1e-30)
    intensity=np.sum(np.abs(actual)**2)/max(np.sum(np.abs(ref)**2),1e-30)
    a,av,_=stokes(target)
    b,bv,_=stokes(restored)
    valid=disk&av&bv
    error=None
    if valid.any():
        dots=np.clip(np.sum(a[:,valid]*b[:,valid],axis=0),-1,1)
        error=float(np.mean(np.arccos(dots)))
    return {"source":SOURCE,"N":N,"twist_angle_deg":angle,
            "grid_size":n,"z_m":z,"obstacle_radius_fraction":obstacle,
            "selected_wavelength_m":532e-9,"selected_field_width_m":.003,
            "affected_region_relative_field_error":float(err),
            "affected_region_intensity_ratio":float(intensity),
            "affected_region_mean_poincare_angle_rad":error,
            "maxwell_residual_max":max([*r0.values(),*rt.values(),*rb.values()]),
            "free_propagation_full_E_norm_ratio":float(np.linalg.norm(first)/np.linalg.norm(target))}

def test():
    cases=[]
    for N,angle in ((3,13.2),(4,16.26),(6,13.2)):
        for z in (0.,.2,.5):
            r=case(N=N,angle=angle,z=z)
            assert r["maxwell_residual_max"]<1e-12,r
            assert abs(r["free_propagation_full_E_norm_ratio"]-1)<1e-10,r
            cases.append(r)
    for n in (96,128,192,256):
        r=case(n=n,z=.5)
        assert r["affected_region_relative_field_error"]<.01,r
        cases.append(r)
    return {"source":SOURCE,"synthetic_Maxwell_suite":"PASS",
            "test_count":len(cases),"cases":cases}

if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("--test",action="store_true")
    p.add_argument("--n",type=int,default=128)
    p.add_argument("--N",type=int,default=6)
    p.add_argument("--angle",type=float,default=13.2)
    p.add_argument("--z",type=float,default=.5)
    a=p.parse_args()
    print(json.dumps(test() if a.test else case(a.n,a.N,a.angle,a.z),indent=2))
