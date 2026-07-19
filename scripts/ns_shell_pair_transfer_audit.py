#!/usr/bin/env python3
"""Scalable exact shell-pair transfer audit for finite Galerkin states.

The velocity is partitioned into dyadic shells before evaluating every ordered
bilinear pair P_K[(u_a . grad)u_b]. Signed and absolute target-mode transfer are
then aggregated per shell pair. This is not the atomwise gross census: it keeps
all cancellation internal to each shell pair and is intended to scale to
matched N32/N48/N64 experiments.
"""
from __future__ import annotations
import argparse,json,math,os,tempfile
from pathlib import Path
from typing import Any
import numpy as np
from ns_galerkin_coherence_core import frequency_grid,leray_project_hat,packet_mask,spectral_gradient

def atomic(path:Path,payload:dict[str,Any],pretty=False):
    path.parent.mkdir(parents=True,exist_ok=True)
    with tempfile.NamedTemporaryFile('w',encoding='utf-8',dir=path.parent,delete=False) as h:
        tmp=Path(h.name);json.dump(payload,h,indent=2 if pretty else None,sort_keys=True);h.write('\n');h.flush();os.fsync(h.fileno())
    try:os.replace(tmp,path)
    finally:
        if tmp.exists():tmp.unlink()

def shell_pair_metrics(raw:np.ndarray,nu:float,target_shell:int,radius:int=1)->dict[str,Any]:
    if raw.ndim!=4 or raw.shape[-1]!=3 or len(set(raw.shape[:3]))!=1:raise ValueError('invalid raw_hat shape')
    n=raw.shape[0];wave,norm2,norm,dealias=frequency_grid(n);retained=leray_project_hat(raw*dealias[...,None],wave,norm2);target=packet_mask(norm,target_shell,dealias);target_hat=retained*target[...,None]
    labels=np.full(norm.shape,-999,int);labels[norm==0]=-1;positive=(norm>0)&dealias;labels[positive]=np.floor(np.log2(norm[positive])).astype(int);shells=sorted(int(x) for x in np.unique(labels[dealias]))
    physical={};gradients={}
    for shell in shells:
        hat=retained*(labels==shell)[...,None];physical[shell]=np.fft.ifftn(hat,axes=(0,1,2)).real;gradients[shell]=spectral_gradient(hat,wave)
    groups=[];signed_sum=gross_sum=0.;pair_forcing=np.zeros_like(retained)
    scale=float(n**3);target_field=target_hat/scale
    for left in shells:
        for right in shells:
            convection=np.einsum('...j,...ij->...i',physical[left],gradients[right]);forcing=leray_project_hat(-np.fft.fftn(convection,axes=(0,1,2))*dealias[...,None],wave,norm2)*target[...,None];pair_forcing+=forcing
            modal=2*(2**target_shell)*np.real(np.sum(np.conjugate(target_field)*(forcing/scale),axis=-1));signed=float(np.sum(modal[target]));gross=float(np.sum(np.abs(modal[target])));signed_sum+=signed;gross_sum+=gross
            groups.append({'left_shell':left,'right_shell':right,'left_shell_offset':left-target_shell,'right_shell_offset':right-target_shell,'signed_rate':signed,'aggregate_modal_gross_activity':gross,'target_mode_count':int(np.count_nonzero(target))})
    u=np.fft.ifftn(retained,axes=(0,1,2)).real;full_grad=spectral_gradient(retained,wave);full_conv=np.einsum('...j,...ij->...i',u,full_grad);direct=leray_project_hat(-np.fft.fftn(full_conv,axes=(0,1,2))*dealias[...,None],wave,norm2)*target[...,None];direct_modal=2*(2**target_shell)*np.real(np.sum(np.conjugate(target_field)*(direct/scale),axis=-1));direct_signed=float(np.sum(direct_modal[target]));direct_gross=float(np.sum(np.abs(direct_modal[target])));energy=np.sum(np.abs(target_field)**2,axis=-1);diss=float(np.sum(norm2[target]*energy[target]));gamma=max(direct_signed,0)/(2*nu*diss) if diss>0 else None
    local=sum(g['aggregate_modal_gross_activity'] for g in groups if abs(g['left_shell_offset'])<=radius and abs(g['right_shell_offset'])<=radius)
    return {'cutoff':n,'target_shell':target_shell,'physical_viscosity':nu,'shells':shells,'shell_pair_groups':sorted(groups,key=lambda g:g['aggregate_modal_gross_activity'],reverse=True),'aggregate_pair_gross_activity':gross_sum,'local_shell_pair_gross_fraction':local/gross_sum if gross_sum>0 else None,'tightness_radius':radius,'direct_packet_signed_rate':direct_signed,'direct_packet_modal_gross_activity':direct_gross,'packet_dissipation':diss,'gamma':gamma,'signed_pair_sum_residual':abs(signed_sum-direct_signed),'forcing_pair_sum_max_residual':float(np.max(np.abs(pair_forcing-direct))),'gross_semantics':'absolute target-mode transfer after aggregation within each ordered shell pair','atomwise_gross_equivalence':False,'truth_authority':False,'theorem_authority':False,'promoted':False}

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--state',type=Path,required=True);p.add_argument('--target-shell',type=int,required=True);p.add_argument('--tightness-radius',type=int,default=1);p.add_argument('--output-json',type=Path,required=True);p.add_argument('--pretty',action='store_true');a=p.parse_args()
    with np.load(a.state,allow_pickle=False) as d:raw=np.asarray(d['raw_hat'],complex);nu=float(d['nu']) if 'nu' in d else 1e-3;time=float(d['time']) if 'time' in d else None
    result=shell_pair_metrics(raw,nu,a.target_shell,a.tightness_radius);result['source_state']=str(a.state);result['time']=time;atomic(a.output_json,result,a.pretty);print(json.dumps({'output_json':str(a.output_json),'gamma':result['gamma'],'local_shell_pair_gross_fraction':result['local_shell_pair_gross_fraction']},sort_keys=True))
if __name__=='__main__':main()
