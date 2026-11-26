"""Original common-clock E4 radial covectors and source primitive BIDI weld.
Reuse native transpose, original source owners, LVII overlap and jet observer.
Finite discrete dual, not a continuum sign or propagated interval certificate.
"""
import argparse,hashlib,json,math,time
from pathlib import Path
import numpy as np
from scipy.integrate import quad
from scipy.interpolate import PchipInterpolator
from check_f8_common_clock_radial_dual import geometry,jet_weights,observer
from check_f8_mode3_window_dual import euler_transpose,coeff,coefficients
from run_f8_common_clock_capture import T0,nt,dt,weight
from run_f8_p0_native_receiver_state_capture import atomic_npz
from ksw668_f8_fv_source_flux import primitives,compact_bump,exact_cell_averages
from ksw668_f8_weak_source import weak_source

EPS=.04

def sha(x):return hashlib.sha256(x).hexdigest()

def run(kind,work,budget):
    dr=.008 if kind=='coarse' else .006;h=.012
    nr=math.ceil(3.01/dr)+1;ny=math.ceil(2.01/h)+1;shape=(3,3,ny,nr)
    cp,cm=coefficients(nr);w,L=jet_weights(dr,nr)
    identity=json.dumps(dict(kind=kind,dr=dr,dy=h,dt=dt,nt=nt,code=sha(Path(__file__).read_bytes()),weights=sha(w.tobytes()+L.tobytes()),owners={p:sha(Path(__file__).with_name(p).read_bytes()) for p in ('check_f8_common_clock_radial_dual.py','check_f8_mode3_window_dual.py','run_f8_common_clock_capture.py','ksw668_f8_tt_multipole.py','ksw668_f8_fv_source_flux.py','ksw668_f8_weak_source.py')}),sort_keys=True)
    work.mkdir(parents=True,exist_ok=True);p=work/(kind+'.source-kernel.npz');lam=np.zeros(shape);kappa=np.zeros((3,3,nr));n=nt-1
    if p.exists():
        with np.load(p,allow_pickle=False) as z:
            assert z['identity'].item()==identity;n=int(z['n'].item());lam=z['lam'].copy();kappa=z['kappa'].copy()
    norm=quad(lambda x:math.exp(1-1/(1-x*x)),-1,1,epsabs=1e-13)[0]*.1
    l0=np.empty_like(lam);l1=l0.copy();l2=l0.copy();start=time.monotonic()
    while n>=0:
        T=T0+n*dt;b0,v0,g0=coeff(T);b1,v1,g1=coeff(T+dt);bh,vh,gh=coeff(T+dt/2)
        euler_transpose(lam,l2,dr,h,bh,vh,cp,cm,dt);l2*=2/3
        euler_transpose(l2,l1,dr,h,b1,v1,cp,cm,dt);l1*=.25
        euler_transpose(l1,l0,dr,h,b0,v0,cp,cm,dt)
        if g0 or g1 or gh:
            for j,(a,g,f) in enumerate(((l1,g0,1.),(l2,g1,.25),(lam,gh,2/3))):kappa[j]+=(-4*dt/h)*g*f*a[2,:,0,:]
        lam=lam/3+.75*l2+l0
        q=weight(T)
        if q:lam+=dt*q/norm*observer(shape,b0,v0,dr,h,cp,cm,w,L)
        n-=1
        if (nt-n)%32==0 and time.monotonic()-start>=budget:break
    assert np.isfinite(lam).all() and np.isfinite(kappa).all();atomic_npz(p,identity=identity,n=n,lam=lam,kappa=kappa);print(kind,n,flush=True)
    return 75 if n>=0 else 0


def volume(dr,n,d):
    j=np.arange(n);return ((dr*(j+.5))**d-(dr*np.maximum(j-.5,0))**d)/d


def pair(q,dr,i,kind):
    # q is a mass-normalized dual covector on active radial nodes.
    d=3+4*i;h=dr/EPS;p=primitives()[i]
    pf=lambda x:0. if x<=0 or x>=1 else float(p(x))
    bump=lambda x:27*x*x*compact_bump(x)
    terms=[]
    if kind=='cell':
        for j in range(len(q)):
            x=(j+.5)*h
            if x>=1:break
            terms.append(-pf(x)*(q[j+1]-q[j]))
        if i==2:
            for j in range(len(q)):
                a=max(0.,(j-.5)*h);b=min(1.,(j+.5)*h)
                if a>=b:break
                terms.append(q[j]*quad(bump,a,b,epsabs=1e-13)[0])
    elif kind=='hat':
        for j in range(len(q)-1):
            a=j*h;b=(j+1)*h;c=min(b,1.)
            if a>=c:break
            slope=(q[j+1]-q[j])/(b*b-a*a)
            terms.append(-slope*quad(lambda x:2*x*pf(x),a,c,epsabs=1e-12,epsrel=1e-11)[0])
            if i==2:terms.append(quad(lambda x:bump(x)*(q[j]+slope*(x*x-a*a)),a,c,epsabs=1e-12,epsrel=1e-11)[0])
    elif kind=='pchip':
        n=min(len(q),math.ceil(1/h)+2);x=(h*np.arange(n))**2;f=PchipInterpolator(x,q[:n]);df=f.derivative()
        for j in range(n-1):
            a=j*h;c=min((j+1)*h,1.)
            if a>=c:break
            terms.append(-quad(lambda u:pf(u)*2*u*df(u*u),a,c,epsabs=1e-12,epsrel=1e-11)[0])
            if i==2:terms.append(quad(lambda u:bump(u)*f(u*u),a,c,epsabs=1e-12,epsrel=1e-11)[0])
    else:raise ValueError(kind)
    t=EPS**d*np.array(terms);return dict(signed=float(t.sum()),absolute=float(abs(t).sum()),terms=t.tolist())


def reconcile(work,old):
    sc,sf,mapped,maps,checks=geometry();rows={};kernels={}
    for kind,dr,src in [('coarse',.008,sc),('fine',.006,sf)]:
        with np.load(work/(kind+'.source-kernel.npz'),allow_pickle=False) as z:
            assert z['n'].item()==-1;identity=json.loads(z['identity'].item());kappa=z['kappa'].copy()
        k=kappa.sum(axis=0);kernels[kind]=k;expected=json.loads((old/(kind+'.E4.json')).read_text());direct=np.einsum('qr,sqr->sq',k,src)
        err=abs(direct-np.array(expected['signed'])[:2])/np.maximum(np.array(expected['absolute'])[:2],1e-300);assert err.max()<1e-9
        rr=[]
        for i,d in enumerate((3,7,11)):
            q=k[i,:-1]/volume(dr,k.shape[1]-1,d);p={s:pair(q,dr,i,s) for s in ('cell','hat','pchip')}
            for j,s in enumerate(('cell','hat')):
                e=abs(p[s]['signed']-direct[j,i])/max(p[s]['absolute'],abs(direct[j,i]),1e-300);assert e<2e-8,(kind,i,s,e)
            rr.append(dict(d=d,dual_nodes=q[:math.ceil(EPS/dr)+2].tolist(),pairings=p))
        rows[kind]=dict(identity=identity,kappa_by_stage=kappa.tolist(),direct=direct.tolist(),max_scaled_replay_error=float(err.max()),rows=rr)
    split=[];k=kernels['fine']
    for i,d in enumerate((3,7,11)):
        qc=k[i,:-1]/volume(.006,k.shape[1]-1,d);ka=maps[i].T@k[i,:-1];qa=ka/volume(.008,len(ka),d)
        for j,s in enumerate(('cell','hat')):
            fine=pair(qc,.006,i,s);pulled=pair(qa,.008,i,s);direct=float(k[i]@(sf[j,i]-mapped[j,i]));pred=fine['signed']-pulled['signed'];scale=fine['absolute']+pulled['absolute'];err=abs(pred-direct)/max(scale,1e-300);assert err<2e-8
            split.append(dict(d=d,source=s,direct=direct,predicted=pred,scaled_error=err,absolute_primitive_budget=scale,pulled_dual_nodes=qa[:7].tolist(),fine=fine,pulled=pulled))
    out=dict(scope='actual finite common-clock E4 source covectors, BV primitive and hat pairings; PCHIP is diagnostic intervention, not certified continuum dual',runs=rows,source_split=split)
    (work/'source_primitive.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(dict(replay={k:v['max_scaled_replay_error'] for k,v in rows.items()},split=[{k:v for k,v in x.items() if k not in ('fine','pulled','pulled_dual_nodes')} for x in split],smooth={k:[{s:p['signed'] for s,p in x['pairings'].items()} for x in v['rows']] for k,v in rows.items()}),indent=2))

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('kind',choices=('coarse','fine','reconcile'));p.add_argument('--work',type=Path,default=Path('.local-f8-source-dual'));p.add_argument('--old',type=Path,default=Path('.local-f8-common'));p.add_argument('--budget',type=float,default=12.);a=p.parse_args();assert 0<a.budget<=90
    if a.kind=='reconcile':reconcile(a.work,a.old)
    else:raise SystemExit(run(a.kind,a.work,a.budget))
