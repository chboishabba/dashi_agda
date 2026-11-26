"""LVII radial overlap + actual mode3 SSPRK3 reverse E4 window decomposition.
Fine mapped source and fine-on-coarse jet receiver are explicit interventions.
No continuum error enclosure or physical sign claim.
"""
import argparse,hashlib,inspect,json,math,time
from pathlib import Path
import numpy as np
import sympy as S
from scipy.integrate import quad
from check_f8_lvii_radial_fibre import overlap
from check_f8_mode3_window_dual import euler_transpose,coeff,coefficients
from run_f8_common_clock_capture import T0,Tend,nt,dt,bulk,weight
from check_f8_parity_capture_tail import geometry_rows,radial_rows
from ksw668_f8_fv_source_flux import exact_cell_averages
from ksw668_f8_weak_source import weak_source
from run_f8_p0_native_receiver_state_capture import atomic_npz


def geometry():
    hc,hf=.008,.006;nc=math.ceil(3.01/hc)+1;nf=math.ceil(3.01/hf)+1
    src=lambda h,n:np.stack([exact_cell_averages(.04,np.arange(n)*h,h),weak_source(.04,np.arange(n)*h,h)])
    sc,sf=src(hc,nc),src(hf,nf);mapped=np.zeros_like(sf);maps=[];checks=[]
    for q,d in enumerate((3,7,11)):
        I,wc,wf,*_=overlap(S.Rational(str(hc)),nc-1,S.Rational(str(hf)),nf-1,d);maps.append(I)
        for k in range(2):
            mapped[k,q,:-1]=I@sc[k,q,:-1]
            mc=wc@sc[k,q,:-1];mf=wf@mapped[k,q,:-1];scale=wc@abs(sc[k,q,:-1]);err=abs(mc-mf)/max(scale,1e-300);assert err<1e-14
            checks.append(dict(d=d,source=k,scaled_moment_error=float(err),relative_source_difference=float(np.sqrt(wf@(mapped[k,q,:-1]-sf[k,q,:-1])**2/(wf@sf[k,q,:-1]**2)))))
    return sc,sf,mapped,maps,checks


def jet_weights(dr,nr,maps=None):
    # Use the literal native cubic radial receiver. Pull back the *jet*
    # weights with Euclidean I^T: coarse U/W/W_T remain native coarse jets.
    hd,nd=(.006,math.ceil(3.01/.006)+1) if maps is not None else (dr,nr)
    ids,w,L,_=radial_rows(bulk-.012,hd,.04,nd)
    W=np.zeros((3,nd));D=W.copy();W[:,ids]=w;D[:,ids]=L
    if maps is None:return W,D
    out=np.zeros((3,nr));lap=out.copy()
    for q,I in enumerate(maps):out[q,:-1]=I.T@W[q,:-1];lap[q,:-1]=I.T@D[q,:-1]
    return out,lap


def observer(shape,b,v,dr,h,cp,cm,w,L):
    t=1/b;a,c=1+v,1-v;A,B,_,_,_,D,_=geometry_rows(t)[0]
    o=np.zeros(shape);seed=np.zeros(shape);z=np.empty_like(seed);acc=t**3/(1+t*t)**2
    o[0,:,0]=D*L;o[1,:,0]=(A*a+B*acc)*w/2;o[2,:,0]=(A*c-B*acc)*w/2
    seed[1,:,0]=B*a*w/2;seed[2,:,0]=B*c*w/2
    euler_transpose(seed,z,dr,h,b,v,cp,cm,1.);return o+z-seed


def run(kind,work,budget):
    sc,sf,mapped,maps,checks=geometry();fine=kind=='fine';dr=.006 if fine else .008;h=.012
    src=np.concatenate((sf,mapped,sf-mapped),axis=0) if fine else sc
    nr=src.shape[-1];ny=math.ceil(2.01/h)+1;shape=(3,3,ny,nr);cp,cm=coefficients(nr)
    w,L=jet_weights(dr,nr,maps if kind=='pulled' else None)
    sha=lambda x:hashlib.sha256(x).hexdigest()
    ident=json.dumps(dict(kind=kind,dt=dt,dr=dr,dy=h,sources=sha(src.tobytes()),weights=sha(w.tobytes()+L.tobytes()),overlap_function=sha(inspect.getsource(overlap).encode()),code=sha(Path(__file__).read_bytes())),sort_keys=True)
    work.mkdir(parents=True,exist_ok=True);p=work/(kind+'.E4.npz');lam=np.zeros(shape);terms=np.zeros((nt,3,len(src),3));n=nt-1
    if p.exists():
        with np.load(p,allow_pickle=False) as z:
            assert z['identity'].item()==ident;n=int(z['n'].item());lam=z['lam'].copy();terms=z['terms'].copy()
    norm=quad(lambda x:math.exp(1-1/(1-x*x)),-1,1,epsabs=1e-13)[0]*.1;l0=np.empty_like(lam);l1=l0.copy();l2=l0.copy();start=time.monotonic()
    def source(y,g,f):return (-4*dt/h)*g*f*np.einsum('qr,sqr->sq',y[2,:,0,:],src)
    while n>=0:
        T=T0+n*dt;b0,v0,g0=coeff(T);b1,v1,g1=coeff(T+dt);bh,vh,gh=coeff(T+dt/2)
        euler_transpose(lam,l2,dr,h,bh,vh,cp,cm,dt);l2*=2/3
        euler_transpose(l2,l1,dr,h,b1,v1,cp,cm,dt);l1*=.25
        euler_transpose(l1,l0,dr,h,b0,v0,cp,cm,dt)
        if g0 or g1 or gh:terms[n,0]=source(l1,g0,1.);terms[n,1]=source(l2,g1,.25);terms[n,2]=source(lam,gh,2/3)
        lam=lam/3+.75*l2+l0
        q=weight(T)
        if q:lam+=dt*q/norm*observer(shape,b0,v0,dr,h,cp,cm,w,L)
        n-=1
        if (nt-n)%32==0 and time.monotonic()-start>=budget:break
    assert np.isfinite(lam).all() and np.isfinite(terms).all();atomic_npz(p,identity=ident,n=n,lam=lam,terms=terms);print(kind,'remaining',n,flush=True)
    if n>=0:return 75
    signed=terms.sum(axis=(0,1));absolute=abs(terms).sum(axis=(0,1));errors=[]
    if kind!='pulled':
        for i,label in enumerate(('C0','C1') if fine else ('A0','A1')):
            q=work/(label+'.axis.json')
            if q.exists():
                actual=np.array(json.loads(q.read_text())['window_signed'])[0,1,0];err=abs(signed[i]-actual)/np.maximum(absolute[i],1e-300);assert err.max()<2e-9;errors.append(dict(label=label,actual=actual.tolist(),scaled_error=float(err.max())))
    if fine:
        err=abs(signed[:2]-signed[2:4]-signed[4:])/np.maximum(absolute[:2]+absolute[2:4]+absolute[4:],1e-300);assert err.max()<1e-12
    report=dict(kind=kind,identity=json.loads(ident),source_order=['cell','weak','mapped_cell','mapped_weak','cell_delta','weak_delta'] if fine else ['cell','weak'],signed=signed.tolist(),absolute=absolute.tolist(),signed_by_stage=terms.sum(axis=0).tolist(),absolute_by_stage=abs(terms).sum(axis=0).tolist(),checks=checks,forward_comparison=errors,checkpoint_sha256=sha(p.read_bytes()),scope='finite original common-clock E4 window reverse; pulled fine cubic observer on native coarse jet; no continuum sign')
    (work/(kind+'.E4.json')).write_text(json.dumps(report,indent=2)+'\n');return 0


def reconcile(work):
    get=lambda k:json.loads((work/(k+'.E4.json')).read_text());a,p,c=map(get,('coarse','pulled','fine'));A,P,C=np.array(a['signed']),np.array(p['signed']),np.array(c['signed']);actual=[]
    for i in range(2):
        coarse=np.array(json.loads((work/('A'+str(i)+'.axis.json')).read_text())['window_signed'])[0,1,0];fine=np.array(json.loads((work/('C'+str(i)+'.axis.json')).read_text())['window_signed'])[0,1,0];actual.append(fine-coarse)
    actual=np.array(actual);source=C[4:];transport=C[2:4]-P;observer_delta=P-A;pred=source+transport+observer_delta;scale=np.array(c['absolute'])[:2]+np.array(a['absolute']);err=abs(pred-actual)/np.maximum(scale,1e-300);assert err.max()<2e-9
    out=dict(scope='original common-clock E4 signed source/transport/observer intervention; transport includes unmatched outer active shells and mapped jet evolution, no continuum error bound',source=source.tolist(),transport=transport.tolist(),observer=observer_delta.tolist(),predicted=pred.tolist(),actual=actual.tolist(),max_scaled_error=float(err.max()),runs=[a,p,c]);(work/'radial.E4.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='runs'},indent=2))

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('kind',choices=('coarse','pulled','fine','reconcile'));p.add_argument('--work',type=Path,default=Path('.local-f8-common'));p.add_argument('--budget',type=float,default=12.);a=p.parse_args();assert 0<a.budget<=90
    if a.kind=='reconcile':reconcile(a.work)
    else:raise SystemExit(run(a.kind,a.work,a.budget))
