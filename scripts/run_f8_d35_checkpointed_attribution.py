"""D3.5 bounded-memory same-clock original receiver attribution.
Separate experimental paired/ledger runs; not historical native receipts.
"""
import argparse, hashlib, json, math, os, time
from pathlib import Path
import numpy as np
from scipy.optimize import brentq
from check_f8_d34_signed_refinement import transfer_builder, coefficients
from ksw668_f8_tt_multipole import F
from ksw668_f8_fv_source_flux import exact_cell_averages
from ksw668_f8_signed_route_stage import step
from f8_fused_step import step_into
from f8_physical_reverse import reverse_physical, physical_observation, signed_contribution
from warp_native_geometric_receiver import receiver_bank
from warp_israel_affine import radial_source_at_receiver, offsets
from check_f8_signed_window import window_rows
from check_f8_modal_cfl import envelope
from f8_exact_block_replay import reverse_leaves
from check_f8_source_inactive_replay import active as source_active
from check_f8_patch_causal import exterior
from check_f8_shrinking_injection import build as build_patch, read as read_patch, inject as inject_patch

def atomic(path, **arrays):
    tmp=path.with_suffix('.tmp')
    with tmp.open('wb') as f:
        np.savez(f,**arrays);f.flush();os.fsync(f.fileno())
    os.replace(tmp,path)

def digest(x):return hashlib.sha256(np.ascontiguousarray(x).tobytes()).hexdigest()

def run(a):
    work=a.work;work.mkdir(parents=True,exist_ok=True)
    if a.window and a.shrink is not None:raise ValueError('distinct observation consumers')
    if not 0<a.budget<=90 or a.block<1 or not 0<a.dt<.0015:raise ValueError('budget/grid guard')
    T0=F(1);span=F(12)-T0;nt=math.ceil(span/a.dt);h=span/nt;end=nt+1
    # Same physical outer normal boundary: 2.016 is divisible by both spacings.
    drc,drf,dyc,dyf=.008,.006,.012,.009
    nc,nf=math.ceil(3.01/drc)+1,math.ceil(3.01/drf)+1
    # Enlarged same-object reference box: no outer-boundary causal contact through t12.
    # This is opt-in and not a historical production geometry or certified CFL.
    mc,mf=(337,449) if a.enlarged_box else (169,225)
    caps=[envelope(dr,dy,nr-1,a.route)[2] for dr,dy,nr in ((drc,dyc,nc),(drf,dyf,nf))]
    if h>float(min(caps)) and not a.allow_uncertified_cfl:raise ValueError('step exceeds sufficient shifted-generator CFL; select smaller dt')
    if T0+end*h>F(13):raise ValueError('clock exceeds CFL envelope')
    patch_certificate=None if a.shrink is None else [exterior(a.shrink,dr,dy,a.dt) for dr,dy in ((drc,dyc),(drf,dyf))]
    S,maps=transfer_builder(drc,nc,dyc,mc,drf,nf,dyf,mf)
    def coeff(T):
        t=brentq(lambda t:F(t)-T,.5,25)
        v=-1/math.sqrt(1+t*t);q=2*(T-T0)/.065-1
        return v,1/t,-6*math.sqrt(1-v*v)*t*math.exp(1-1/(1-q*q)) if abs(q)<1 else 0.
    # All three actual Shu-Osher clocks; never discard small nonzero forcing.
    source_steps=[]
    for n in range(end):
        T=T0+n*h
        source_steps.append(source_active((coeff(T)[2],coeff(T+h)[2],coeff(T+h/2)[2])))
    def setup(dr,dy,nr,ny):
        src=exact_cell_averages(.04,np.arange(nr)*dr,dr);cp,cm=coefficients(nr,dr)
        initial=np.zeros((6,3,ny,nr))
        if a.fused:
            scratch1,scratch2=np.empty_like(initial),np.empty_like(initial)
            def advance(x,n,source=src):
                # Returned state must own its storage: recursive replay retains ancestors.
                return step_into(x,np.empty_like(x),scratch1,scratch2,T0+n*h,h,coeff,dr,dy,source,cp,cm,a.route)
        else:
            def advance(x,n,source=src):return step(x,T0+n*h,h,coeff,dr,dy,source,cp,cm,a.route)
        return src,advance,initial
    sc,C,xc=setup(drc,dyc,nc,mc);sf,G,xf=setup(drf,dyf,nf,mf)
    sm=np.zeros_like(sf)
    for q,I in enumerate(maps):sm[q,:-1]=I@sc[q,:-1]
    files=['ksw668_f8_tt_multipole.py','ksw668_f8_fv_source_flux.py','ksw668_f8_signed_route_stage.py','ksw668_f8_weighted_normal_stage.py','warp_stage_adjoint.py','warp_native_geometric_receiver.py','warp_israel_affine.py','check_f8_d34_signed_refinement.py','check_f8_lvii_radial_fibre.py','check_f8_signed_window.py','check_f8_modal_cfl.py','check_f8_shrinking_jet.py','check_f8_shrinking_injection.py','f8_exact_block_replay.py','f8_physical_reverse.py','f8_fused_step.py','check_f8_source_inactive_replay.py','check_f8_patch_causal.py','check_f8_causal_rk3_weld.py',Path(__file__).name]
    forward_ident=json.dumps(dict(route=a.route,fused=a.fused,allow_uncertified_cfl=a.allow_uncertified_cfl,cfl_cap=float(min(caps)),enlarged_box=a.enlarged_box,grid=[nc,nf,mc,mf],h=h,nt=nt,block=a.block,sc=digest(sc),sf=digest(sf),sm=digest(sm),files={f:hashlib.sha256(Path(__file__).with_name(f).read_bytes()).hexdigest() for f in files}),sort_keys=True)
    ident=json.dumps(dict(forward_identity=json.loads(forward_ident),window=a.window,shrink=a.shrink,reverse_carrier='physical3'),sort_keys=True)
    consumer_key=hashlib.sha256(ident.encode()).hexdigest()[:24]
    def write(k,c,f):atomic(work/f'forward-{k:08d}.npz',identity=forward_ident,k=k,c=c,f=f,cd=digest(c),fd=digest(f))
    def read(k):
        with np.load(work/f'forward-{k:08d}.npz',allow_pickle=False) as z:
            if z['identity'].item()!=forward_ident or int(z['k'])!=k:raise ValueError('checkpoint identity')
            c,f=z['c'],z['f']
            if c.shape!=xc.shape or f.shape!=xf.shape or digest(c)!=z['cd'].item() or digest(f)!=z['fd'].item() or not np.isfinite(c).all() or not np.isfinite(f).all():raise ValueError('checkpoint integrity')
            return c,f
    # Split at every observation slot as well as block boundaries.
    cuts=sorted(set(range(0,end+1,a.block))|{nt-1,nt,end})
    start=time.monotonic()
    if not (work/'forward-00000000.npz').exists():write(0,xc,xf)
    # Resume at the last contiguous anchor; validate every earlier anchor on reverse replay.
    prefix=0
    for k in cuts[1:]:
        if not (work/f'forward-{k:08d}.npz').exists():break
        prefix+=1
    if any((work/f'forward-{k:08d}.npz').exists() for k in cuts[prefix+1:]):raise ValueError('noncontiguous forward checkpoints')
    c,f=read(cuts[prefix])
    for lo,hi in zip(cuts[prefix:],cuts[prefix+1:]):
        for n in range(lo,hi):c,f=C(c,n),G(f,n)
        write(hi,c,f)
        if time.monotonic()-start>=a.budget:return {'phase':'forward','cursor':hi}
    del c,f
    if a.forward_only:
        return dict(phase='forward_complete',cursor=end,forward_identity=forward_ident,physical_causal_null_certified=False)
    # One observer row at a time. Reverse state and cumulative signed sums are atomic.
    bulk=math.sqrt(span**2-(1-1/12)**2);rxs=(bulk-.012,bulk+.1)
    vel=np.array([coeff(T0+i*h/2)[0] for i in range(2*end+1)])
    def readout(o,x):return np.sum(o*x,axis=(0,2,3))
    results={}
    for pos,rx in enumerate(rxs):
        if a.window:
            ts=np.array([1/coeff(T0+n*h)[1] for n in range(end+1)])
            ic,wc,*_=window_rows(ts,h,rx,.04,drc,nc,span-.15,.10)
            jf,wf,*_=window_rows(ts,h,rx,.04,drf,nf,span-.15,.10)
            # The original SMS row is source-free at both exterior probe radii.
            if np.any(sc[:,ic]) or np.any(sf[:,jf]):raise ValueError('window source-free receiver required')
        elif a.shrink is not None:
            Tgrid=np.arange(end+1)*h;ts=np.array([1/coeff(T0+n*h)[1] for n in range(end+1)])
            pc=build_patch(Tgrid,ts,dyc,mc,drc,nc,rx,a.shrink)
            pf=build_patch(Tgrid,ts,dyf,mf,drf,nf,rx,a.shrink)
            if np.any(sc[:,pc[2]]) or np.any(sf[:,pf[2]]):raise ValueError('source-free patch required')
        else:
            bc=receiver_bank(12,rx,.04,drc,dyc,h,vel,nt,nc,3)
            bf=receiver_bank(12,rx,.04,drf,dyf,h,vel,nt,nf,3)
        gc=radial_source_at_receiver(sc,coeff(T0+nt*h)[2],rx,.04,drc)
        gf=radial_source_at_receiver(sf,coeff(T0+nt*h)[2],rx,.04,drf)
        for ch in range(2 if a.window else 6):
            def obs(n):
                if a.shrink is not None:return physical_observation(inject_patch(pf,ch,n,xf))
                o=np.zeros_like(xf[:3])
                if a.window:o[0,:,0,:][:,jf]=wf[ch,n]
                elif nt-1<=n<=end:o[:,:,:3,:]=bf[ch,n-nt+1]
                if np.any(o[..., -1]):raise ValueError('observer outside active radial carrier')
                return o
            path=work/f'reverse-{consumer_key}-{pos}-{ch}.npz'
            cursor=end;lam=obs(end);signed=np.zeros((2,6,3));absolute=signed.copy()
            mismatch=np.zeros(3);direct=np.zeros(3);coarse_obs=np.zeros(3);fine_obs=np.zeros(3)
            if path.exists():
                with np.load(path,allow_pickle=False) as z:
                    if z['identity'].item()!=ident:raise ValueError('reverse identity')
                    cursor=int(z['cursor']);lam=z['lam'];signed=z['signed'];absolute=z['absolute'];mismatch=z['mismatch'];direct=z['direct'];coarse_obs=z['coarse_obs'];fine_obs=z['fine_obs']
                    if any(digest(z[k])!=z[k+'_sha'].item() for k in ('lam','signed','absolute','mismatch','direct','coarse_obs','fine_obs')):raise ValueError('reverse digest mismatch')
                    if any(x.shape!=(3,) for x in (mismatch,direct,coarse_obs,fine_obs)) or not np.isfinite([mismatch,direct,coarse_obs,fine_obs]).all():raise ValueError('reverse observation integrity')
                    if cursor not in cuts or lam.shape!=xf[:3].shape or signed.shape!=(2,6,3) or absolute.shape!=signed.shape or not all(np.isfinite(x).all() for x in (lam,signed,absolute)):raise ValueError('reverse integrity')
            for lo,hi in reversed(list(zip(cuts,cuts[1:]))):
                if hi>cursor:continue
                c,f=read(lo);ce,fe=read(hi)
                # Recursive exact replay, O(log block) states, no stored defect history.
                # Persist only after all leaves and endpoint checks succeed.
                for n,c0n,f0n,cn,fn in reverse_leaves(lo,hi,c,f,ce,fe,C,G):
                    z=S(c0n)
                    if a.window and (np.any(wc[ch,n]) or np.any(wf[ch,n])):
                        oc=np.sum(wc[ch,n]*c0n[0,:,0,:][:,ic],axis=1)
                        of=np.sum(wf[ch,n]*f0n[0,:,0,:][:,jf],axis=1)
                        oz=np.sum(wf[ch,n]*z[0,:,0,:][:,jf],axis=1)
                        mismatch+=oz-oc;direct+=of-oc;coarse_obs+=oc;fine_obs+=of
                    if a.shrink is not None:
                        oc=read_patch(pc,ch,n,c0n);of=read_patch(pf,ch,n,f0n);oz=read_patch(pf,ch,n,z)
                        mismatch+=oz-oc;direct+=of-oc;coarse_obs+=oc;fine_obs+=of
                    aa=G(z,n);bb=G(z,n,sm) if source_steps[n] else aa;cc=S(cn)
                    for j,d in enumerate((aa-bb,bb-cc)):
                        value=signed_contribution(lam,d)
                        signed[j]+=value;absolute[j]+=abs(value)
                    lam=obs(n)+reverse_physical(lam,T0+n*h,h,coeff,drf,dyf,a.route)
                del c,f,ce,fe,c0n,f0n,cn,fn,z,aa,bb,cc,d
                cursor=lo
                arrays=dict(lam=lam,signed=signed,absolute=absolute,mismatch=mismatch,direct=direct,coarse_obs=coarse_obs,fine_obs=fine_obs)
                atomic(path,identity=ident,cursor=cursor,**arrays,**{k+'_sha':digest(v) for k,v in arrays.items()})
                if time.monotonic()-start>=a.budget:return {'phase':'reverse','probe':pos,'row':ch,'cursor':cursor}
            c0,f0=read(0);initial=readout(lam,(f0-S(c0))[:3])
            if a.window:
                if np.any(wc[ch,end]) or np.any(wf[ch,end]):raise ValueError('terminal window support')
                off=np.zeros(3)
            elif a.shrink is not None:
                if np.any(obs(end)):raise ValueError('terminal patch support')
                off=np.zeros(3)
            else:
                mismatch=np.zeros(3);direct=np.zeros(3);coarse_obs=np.zeros(3);fine_obs=np.zeros(3)
                for i,n in enumerate((nt-1,nt,end)):
                    c,f=read(n)
                    oc=readout(bc[ch,i],c[:3,:,:3,:]);of=readout(bf[ch,i],f[:3,:,:3,:])
                    mismatch+=readout(bf[ch,i],S(c)[:3,:,:3,:])-oc
                    direct+=of-oc;coarse_obs+=oc;fine_obs+=of
                off=offsets(gf)[ch]-offsets(gc)[ch];direct+=off
                coarse_obs+=offsets(gc)[ch];fine_obs+=offsets(gf)[ch]
            pred=initial+signed.sum(axis=(0,1))+mismatch+off
            bound=abs(initial)+absolute.sum(axis=(0,1))+abs(mismatch)+abs(off)
            if np.any(signed[:,3:]) or np.any(absolute[:,3:]):raise ValueError('physical-only ledger has nonzero history contribution')
            if not np.all(np.isfinite([direct,pred,bound])) or not np.all(abs(pred-direct)<=1e-8*np.maximum(1.,bound)):raise ValueError('endpoint ledger mismatch')
            obs_scale=np.maximum(1.,np.maximum(abs(coarse_obs),abs(fine_obs))+bound)
            if not np.all(abs(fine_obs-coarse_obs-direct)<=1e-8*obs_scale):raise ValueError('independent receiver totals disagree')
            results[f'{pos}:{ch}']=dict(coarse=coarse_obs.tolist(),fine=fine_obs.tolist(),initial=initial.tolist(),signed=signed.tolist(),absolute=absolute.tolist(),observer=mismatch.tolist(),offset=off.tolist(),total=direct.tolist(),bound=bound.tolist())
    return dict(phase='complete_experiment',identity=ident,forward_identity=forward_ident,consumer_key=consumer_key,results=results,far_patch_support_certificate=patch_certificate,source_active_steps=sum(source_steps),source_inactive_steps=end-sum(source_steps),physical_causal_null_certified=False)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('work',type=Path);p.add_argument('--route',choices=['paired','ledger'],required=True);p.add_argument('--dt',type=float,default=.0006);p.add_argument('--allow-uncertified-cfl',action='store_true',help='diagnostic override of sufficient CFL envelope');p.add_argument('--block',type=int,default=32,help='anchor stride; recursive replay uses logarithmic block storage');p.add_argument('--budget',type=float,default=75);p.add_argument('--fused',action='store_true',help='opt-in tested full-carrier fused step; separate checkpoint identity');p.add_argument('--forward-only',action='store_true',help='complete shared forward anchors without starting receiver reverse');g=p.add_mutually_exclusive_group();g.add_argument('--window',action='store_true',help='fixed compact E4/SMS window');g.add_argument('--shrink',type=float,help='independent seven-jet patch width in bulk coordinate units');p.add_argument('--enlarged-box',action='store_true',help='normal extent 4.032; causal reference compatible, not certified production CFL')
    a=p.parse_args();r=run(a);print(json.dumps(r));raise SystemExit(0 if r['phase'] in ('complete_experiment','forward_complete') else 75)
