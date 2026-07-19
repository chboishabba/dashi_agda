#!/usr/bin/env python3
"""Generate matched periodic Galerkin NS trajectories at several cutoffs.

The same divergence-free initial field is represented at every cutoff. The
`triad-excursion` initial condition places two shell-(K-1) inputs and one shell-K
output in a phase configuration with positive packet transfer, so the matched
baseline exercises the dangerous-Gamma lane rather than passing vacuously.
"""
from __future__ import annotations
import argparse,json,math,os,tempfile
from pathlib import Path
from typing import Any
import numpy as np
from ns_galerkin_coherence_core import frequency_grid,galerkin_packet_rhs_components,leray_project_hat,nonlinear_momentum_components

def ints(raw:str)->tuple[int,...]:
    out=tuple(sorted({int(x.strip()) for x in raw.split(',') if x.strip()}))
    if not out or any(x<8 for x in out):raise ValueError('cutoffs must be at least 8')
    return out

def atomic(path:Path,payload:dict[str,Any])->None:
    path.parent.mkdir(parents=True,exist_ok=True)
    with tempfile.NamedTemporaryFile('w',encoding='utf-8',dir=path.parent,delete=False) as h:
        tmp=Path(h.name);json.dump(payload,h,indent=2,sort_keys=True);h.write('\n');h.flush();os.fsync(h.fileno())
    try:os.replace(tmp,path)
    finally:
        if tmp.exists():tmp.unlink()

def taylor_green_initial_hat(n:int,base_wave:int,amplitude:float)->np.ndarray:
    coordinate=2*np.pi*np.arange(n)/n;z,y,x=np.meshgrid(coordinate,coordinate,coordinate,indexing='ij');m=float(base_wave);velocity=np.zeros((n,n,n,3),float)
    velocity[...,0]=amplitude*np.sin(m*x)*np.cos(m*y)*np.cos(m*z);velocity[...,1]=-amplitude*np.cos(m*x)*np.sin(m*y)*np.cos(m*z)
    return np.fft.fftn(velocity,axes=(0,1,2))

def triad_excursion_initial_hat(n:int,input_amplitude:float,target_amplitude:float)->np.ndarray:
    """Reality-closed p+q=k triad with p,q in shell 1 and k in shell 2."""
    if n/3<3:raise ValueError('triad-excursion requires dealiased component 3')
    raw=np.zeros((n,n,n,3),complex);scale=float(n**3);p=(3,0,1);q=(0,3,1);k=(3,3,2)
    vp=np.asarray((0.,1.,0.));vq=np.asarray((1.,0.,0.));vk=np.asarray((6.,6.,-18.))/11
    def put(mode,coefficient):
        x,y,z=mode;raw[z%n,y%n,x%n]=scale*coefficient;raw[(-z)%n,(-y)%n,(-x)%n]=scale*np.conjugate(coefficient)
    put(p,input_amplitude*vp);put(q,input_amplitude*vq);put(k,-1j*target_amplitude*vk)
    return raw

def initial_hat(n:int,kind:str,base_wave:int,amplitude:float,target_amplitude:float)->np.ndarray:
    if kind=='taylor-green':return taylor_green_initial_hat(n,base_wave,amplitude)
    if kind=='triad-excursion':return triad_excursion_initial_hat(n,amplitude,target_amplitude)
    raise ValueError(f'unknown initial condition {kind}')

def rhs(raw:np.ndarray,nu:float)->np.ndarray:
    n=raw.shape[0];wave,norm2,_norm,dealias=frequency_grid(n);retained=leray_project_hat(raw*dealias[...,None],wave,norm2);adv,pressure=nonlinear_momentum_components(retained,wave,norm2,dealias)
    return adv+pressure-nu*norm2[...,None]*retained

def rk4(raw:np.ndarray,dt:float,nu:float)->np.ndarray:
    k1=rhs(raw,nu);k2=rhs(raw+.5*dt*k1,nu);k3=rhs(raw+.5*dt*k2,nu);k4=rhs(raw+dt*k3,nu);updated=raw+dt*(k1+2*k2+2*k3+k4)/6
    wave,norm2,_norm,dealias=frequency_grid(raw.shape[0]);return leray_project_hat(updated*dealias[...,None],wave,norm2)

def packet_gamma(raw:np.ndarray,nu:float,shell:int)->float|None:
    data=galerkin_packet_rhs_components(raw,nu,shell);n=raw.shape[0];field=data['packet_hat']/float(n**3);nonlinear=sum((value for name,value in data['components'].items() if name!='viscous'),np.zeros_like(field))/float(n**3);packet=data['packet'];norm2=data['norm_sq'];d=float(np.sum(norm2[packet]*np.sum(np.abs(field[packet])**2,axis=-1)))
    if d<=1e-30:return None
    q=float(2*(2**shell)*np.real(np.sum(np.conjugate(field[packet])*nonlinear[packet])));return max(q,0)/(2*nu*d)

def stable_dt(raw:np.ndarray,nu:float,cfl:float,max_dt:float)->float:
    n=raw.shape[0];u=np.fft.ifftn(raw,axes=(0,1,2)).real;speed=float(np.max(np.linalg.norm(u,axis=-1)));kmax=n/3;denominator=speed*kmax+nu*kmax*kmax
    return min(max_dt,cfl/denominator if denominator>0 else max_dt)

def run_one(n:int,outdir:Path,*,nu:float,shell:int,end_time:float,base_wave:int,amplitude:float,cfl:float,nominal_output_dt:float,threshold:float,near_band:float,dense_factor:int,initial_condition:str='triad-excursion',target_amplitude:float=.25)->dict[str,Any]:
    raw=initial_hat(n,initial_condition,base_wave,amplitude,target_amplitude);wave,norm2,_norm,dealias=frequency_grid(n);raw=leray_project_hat(raw*dealias[...,None],wave,norm2);time=0.;next_nominal=0.;states=[];step=0
    while True:
        gamma=packet_gamma(raw,nu,shell);near=gamma is not None and gamma>=max(threshold-near_band,0);should_save=not states or time>=next_nominal-1e-13 or near or time>=end_time-1e-13
        if should_save:
            path=outdir/f'N{n}_t{len(states):05d}.npz';np.savez(path,raw_hat=raw,nu=np.asarray(nu),time=np.asarray(time),target_shell=np.asarray(shell));states.append({'source_state':str(path),'time':time,'gamma_at_save':gamma,'cutoff':n,'target_shell':shell,'adaptive_dense':near});next_nominal=max(next_nominal+nominal_output_dt,time+nominal_output_dt)
        if time>=end_time-1e-13:break
        max_dt=nominal_output_dt/(dense_factor if near else 1);dt=min(stable_dt(raw,nu,cfl,max_dt),end_time-time)
        if dt<=0 or not math.isfinite(dt):raise RuntimeError('nonpositive integration step')
        raw=rk4(raw,dt,nu);time+=dt;step+=1
        if step>100000:raise RuntimeError('integration step limit exceeded')
    return {'cutoff':n,'trajectory_id':f'matched-N{n}','state_count':len(states),'integration_step_count':step,'initial_gamma':states[0]['gamma_at_save'],'maximum_saved_gamma':max((s['gamma_at_save'] for s in states if s['gamma_at_save'] is not None),default=None),'states':states}

def generate(cutoffs:tuple[int,...],outdir:Path,**kwargs:Any)->dict[str,Any]:
    outdir.mkdir(parents=True,exist_ok=True);runs=[run_one(n,outdir,**kwargs) for n in cutoffs]
    return {'schema_version':'1.1.0','authority':{'finite_galerkin_trajectory':True,'continuum_authority':False,'truth_authority':False,'theorem_authority':False,'bkm_authority':False,'clay_authority':False,'promoted':False},'initial_condition':{'kind':kwargs.get('initial_condition','triad-excursion'),'base_wave':kwargs['base_wave'],'input_amplitude':kwargs['amplitude'],'target_amplitude':kwargs.get('target_amplitude',.25)},'physical_parameters':{'viscosity':kwargs['nu'],'target_shell':kwargs['shell'],'end_time':kwargs['end_time'],'gamma_dense_threshold':kwargs['threshold']},'runs':runs,'matched_cutoffs':[r['cutoff'] for r in runs]}

def main()->None:
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--cutoffs',default='32,48,64');p.add_argument('--output-dir',type=Path,required=True);p.add_argument('--manifest-json',type=Path,required=True);p.add_argument('--viscosity',type=float,default=.01);p.add_argument('--target-shell',type=int,default=2);p.add_argument('--end-time',type=float,default=.05);p.add_argument('--initial-condition',choices=('triad-excursion','taylor-green'),default='triad-excursion');p.add_argument('--base-wave',type=int,default=3);p.add_argument('--amplitude',type=float,default=.1);p.add_argument('--target-amplitude',type=float,default=.25);p.add_argument('--cfl',type=float,default=.2);p.add_argument('--output-dt',type=float,default=.01);p.add_argument('--gamma-dense-threshold',type=float,default=.5);p.add_argument('--near-band',type=float,default=.1);p.add_argument('--dense-factor',type=int,default=4);a=p.parse_args()
    result=generate(ints(a.cutoffs),a.output_dir,nu=a.viscosity,shell=a.target_shell,end_time=a.end_time,base_wave=a.base_wave,amplitude=a.amplitude,cfl=a.cfl,nominal_output_dt=a.output_dt,threshold=a.gamma_dense_threshold,near_band=a.near_band,dense_factor=a.dense_factor,initial_condition=a.initial_condition,target_amplitude=a.target_amplitude);atomic(a.manifest_json,result);print(json.dumps({'manifest_json':str(a.manifest_json),'run_count':len(result['runs']),'state_count':sum(r['state_count'] for r in result['runs']),'initial_gammas':[r['initial_gamma'] for r in result['runs']]},sort_keys=True))
if __name__=='__main__':main()
