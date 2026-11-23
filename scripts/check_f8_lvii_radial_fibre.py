"""Weighted radial identification and finite source/transport/receiver attribution.
Uses original native stage and literal original receiver; diagnostic source swap
is NOT an accepted physical source. Zero extension at the outer active boundary.
Run in bounded chunks: python check_f8_lvii_radial_fibre.py WORK --budget 12
"""
import argparse, ast, hashlib, inspect, json, math, os, tempfile, time
from pathlib import Path
import numpy as np
import sympy as s
from scipy.sparse import csr_matrix, diags
import ksw668_f8_tt_multipole as native
from ksw668_f8_fv_source_flux import exact_cell_averages
from ksw668_f8_ssprk_checkpoint import NativeCheckpoint


def cells(h,n):
    return [(max(0,(j-s.Rational(1,2))*h),(j+s.Rational(1,2))*h) for j in range(n)]


def overlap(hc,nc,hf,nf,d):
    C,F=cells(hc,nc),cells(hf,nf)
    mass=lambda a,b:(b**d-a**d)/d
    wc=[mass(*q) for q in C]; wf=[mass(*q) for q in F]
    entries=[]; i=j=0
    while i<nf and j<nc:
        a,b=max(F[i][0],C[j][0]),min(F[i][1],C[j][1])
        if b>a:entries.append((i,j,mass(a,b)))
        if F[i][1]<=C[j][1]:i+=1
        else:j+=1
    rs=[s.S.Zero]*nf; cs=[s.S.Zero]*nc
    for i,j,v in entries:rs[i]+=v;cs[j]+=v
    assert all(0<=a<=b for a,b in zip(rs,wf))
    assert all(0<=a<=b for a,b in zip(cs,wc))
    assert sum(rs)==sum(cs)==mass(s.S.Zero,min(C[-1][1],F[-1][1]))
    # Weighted transpose: w_f I_fc = overlap = w_c I_cf^T.
    assert all(wf[i]*(v/wf[i])==wc[j]*(v/wc[j]) for i,j,v in entries)
    I=csr_matrix(([float(v/wf[i]) for i,j,v in entries],([i for i,j,v in entries],[j for i,j,v in entries])),shape=(nf,nc))
    return I,np.array(list(map(float,wc))),np.array(list(map(float,wf))),rs,cs,wc,wf


def coefficients(n,dr):
    cp=np.zeros((3,n));cm=np.zeros_like(cp)
    for q in range(3):
        d=3+4*q
        for j in range(1,n):
            den=(j+.5)**d-(j-.5)**d
            cp[q,j]=d*(j+.5)**(d-1)/den;cm[q,j]=d*(j-.5)**(d-1)/den
    return cp,cm


def radial(n,h,d):
    # Active nodes only: outer enforced Dirichlet value is zero.
    p=np.zeros(n);m=np.zeros(n);p[0]=2*d
    for j in range(1,n):
        den=(j+.5)**d-(j-.5)**d
        p[j]=d*(j+.5)**(d-1)/den;m[j]=d*(j-.5)**(d-1)/den
    return diags([m[1:],-(p+m),p[:-1]],[-1,0,1],format='csr')/h**2


def coeff(T,T0,pulse=.065):
    t=max(1.,math.exp(T+1)/2)
    for _ in range(7):
        t-=(native.F(t)-T)/(math.sqrt(1+t*t)/t**2)
        if t<.5:t=.5
    v=-1/math.sqrt(1+t*t);b=1/t;ds=T-T0;q=2*ds/pulse-1
    amp=-6*math.sqrt(1-v*v)/b*math.exp(1-1/(1-q*q)) if 0<ds<pulse else 0.
    return v,b,amp


def load(path):
    with np.load(path,allow_pickle=False) as z:return {k:z[k].copy() for k in z.files}


def receiver(X,walls,config,src):
    dr,dy,dt,t,nt=(config[k] for k in ('dr','dy','dt','final_t','nt'))
    eps=config['eps']; T0=native.F(1);span=native.F(t)-T0
    bulk=math.sqrt(span*span-(1-1/t)**2);rx=bulk-config['inside_chord'];nr=X.shape[-1]
    cp,cm=coefficients(nr,dr);out=np.empty_like(X)
    v,b,amp=coeff(T0+(nt+1)*dt,T0)
    U,P,M=X.copy();native.enforce(U,P,M,v,amp,src,3)
    native.stage(U,P,M,*out,dr,dy,b,v,amp,src,cp,cm,3)
    prev_wall,now_wall,prev_walldot,now_walldot=walls
    next_wall=X[0,:,0,:].copy();next_walldot=out[0,:,0,:].copy();final_t=t
    # Compile the literal existing receiver closure; no alternate Weyl formula.
    tree=ast.parse(inspect.getsource(native.propagate))
    node=next(n for n in ast.walk(tree) if isinstance(n,ast.FunctionDef) and n.name=='read_all')
    module=ast.Module(body=[node],type_ignores=[])
    env=dict(globals());env.update(locals());exec(compile(module,native.__file__,'exec'),env)
    return env['read_all'](rx),env['read_all'](bulk+.1)


def run(work,budget):
    C=load(work/'factorial-A.npz');F=load(work/'factorial-C.npz')
    cc=json.loads(C['identity'].item())['config'];fc=json.loads(F['identity'].item())['config']
    assert all(cc[k]==fc[k] for k in cc if k!='dr')
    nt=fc['nt'];assert C['cursor']==F['cursor']==nt+1
    xc=np.stack([C[k] for k in ('U','P','M')]);xf=np.stack([F[k] for k in ('U','P','M')]);nc=xc.shape[-1];nf=xf.shape[-1]
    hc,hf=s.Rational(str(cc['dr'])),s.Rational(str(fc['dr']))
    sc=exact_cell_averages(.04,np.arange(nc)*float(hc),float(hc));sf=exact_cell_averages(.04,np.arange(nf)*float(hf),float(hf));sm=np.zeros_like(sf)
    maps=[];rng=np.random.default_rng(1527)
    for q in range(3):
        d=3+4*q;I,wc,wf,rs,cs,wce,wfe=overlap(hc,nc-1,hf,nf-1,d);maps.append(I)
        sm[q,:-1]=I@sc[q,:-1]
        x=rng.normal(size=nc-1);y=rng.normal(size=nf-1)
        adj=(I.T@(wf*y))/wc
        assert np.allclose(np.dot(wf*y,I@x),np.dot(wc*x,adj),rtol=1e-12,atol=1e-12)
        assert np.dot(wf,(I@x)**2)<=np.dot(wc,x*x)*(1+1e-13)
        assert np.allclose(np.dot(wf,sm[q,:-1]),np.dot(wc,sc[q,:-1]),rtol=1e-10,atol=1e-12)
        wnorm=lambda x:np.sqrt(np.dot(wf,x*x))
        src_rel=wnorm(sm[q,:-1]-sf[q,:-1])/wnorm(sf[q,:-1])
        # Native r^2 consistency is exact away from the imposed outer node.
        j=s.symbols('j',positive=True,integer=True);p=d*(j+s.Rational(1,2))**(d-1)/((j+s.Rational(1,2))**d-(j-s.Rational(1,2))**d);m=d*(j-s.Rational(1,2))**(d-1)/((j+s.Rational(1,2))**d-(j-s.Rational(1,2))**d)
        assert s.cancel(p*(2*j+1)-m*(2*j-1)-2*d)==0
        # Correction: compare the commutator on a smooth compact polynomial,
        # not on a piecewise-constant discontinuous source alone.
        rc=np.arange(nc-1)*float(hc); rf=np.arange(nf-1)*float(hf)
        u=np.maximum(1-(rc/.12)**2,0)**4
        Ac=radial(nc-1,float(hc),d);Af=radial(nf-1,float(hf),d)
        comm=Af@(I@u)-I@(Ac@u)
        print('ell',2*q,'active extent',float(cells(hc,nc-1)[-1][1]),float(cells(hf,nf-1)[-1][1]),'source relative',src_rel,'smooth comm relative',wnorm(comm)/wnorm(I@(Ac@u)),'source moments',np.dot(wc,sc[q,:-1]),np.dot(wf,sm[q,:-1]),np.dot(wf,sf[q,:-1]),flush=True)
    def transfer(x):
        out=np.zeros((*x.shape[:-1],nf))
        # q axis is third from last for complete state, second for wall history.
        qaxis=x.ndim-3 if x.ndim>=3 else 0
        for q,I in enumerate(maps):
            sl=[slice(None)]*x.ndim;sl[qaxis]=q;sub=x[tuple(sl)][...,:-1];out[tuple(sl)][...,:-1]=(I@sub.reshape(-1,nc-1).T).T.reshape(*sub.shape[:-1],nf-1)
        return out
    # Same original endpoint geometry. Readout replay controls against actual JSON.
    cw=[C['w'+str(i)] for i in range(4)];fw=[F['w'+str(i)] for i in range(4)]
    cr=receiver(xc,cw,cc,sc);fr=receiver(xf,fw,fc,sf)
    # The mapped coarse next tangent must be transported, not reconstructed by
    # the fine RHS: include readout's actual coarse history and lookahead below.
    def mapped_receiver():
        # Map the coarse next tangent as well using actual coarse native RHS.
        cp,cm=coefficients(nc,float(hc));xx=xc.copy();o=np.empty_like(xx);T0=native.F(1);v,b,amp=coeff(T0+(nt+1)*cc['dt'],T0)
        native.enforce(*xx,v,amp,sc,3);native.stage(*xx,*o,float(hc),cc['dy'],b,v,amp,sc,cp,cm,3)
        w=[transfer(a) for a in cw];prev_wall,now_wall,prev_walldot,now_walldot=w
        next_wall=transfer(xc[0,:,0,:]);next_walldot=transfer(o[0,:,0,:]);dr=fc['dr'];dt=fc['dt'];final_t=fc['final_t'];eps=fc['eps'];nr=nf
        tree=ast.parse(inspect.getsource(native.propagate));node=next(n for n in ast.walk(tree) if isinstance(n,ast.FunctionDef) and n.name=='read_all');env=dict(globals());env.update(locals());exec(compile(ast.Module(body=[node],type_ignores=[]),native.__file__,'exec'),env)
        span=native.F(final_t)-T0;bulk=math.sqrt(span*span-(1-1/final_t)**2)
        return env['read_all'](bulk-fc['inside_chord']),env['read_all'](bulk+.1)
    ir=mapped_receiver()
    for name,rr in [('factorial-A',cr),('factorial-C',fr)]:
        old=json.loads((work/(name+'.json')).read_text())
        for key,field in [('mode_E4','receiver_mode_intrinsic_4D_electric_Weyl'),('mode_E5','receiver_mode_projected_5D_electric_Weyl'),('mode_E4_tangent','receiver_mode_intrinsic_4D_electric_Weyl_tangent'),('mode_E5_tangent','receiver_mode_projected_5D_electric_Weyl_tangent')]:
            np.testing.assert_array_equal(rr[0][key],old[field])
    # Full fine evolution with transferred source, an explicit diagnostic intervention.
    # Use native stage/enforce, unchanged physical-state SSPRK3 chronology.
    cp,cm=coefficients(nf,float(hf));dt=fc['dt'];dy=fc['dy'];T0=native.F(1)
    cfg=dict(fc,diagnostic='LVII-mapped-source',diagnostic_script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    ck=NativeCheckpoint(work/'LVII-mapped.npz',cfg,xf.shape[1:],sm,cp,cm)
    got=ck.load();x=np.zeros_like(xf);walls=[None]*4;start=0
    if got is not None:start,*arr=got;x=np.stack(arr[:3]);walls=arr[3:]
    def rhs(x,T):
        v,b,amp=coeff(T,T0);native.enforce(*x,v,amp,sm,3);o=np.empty_like(x);native.stage(*x,*o,float(hf),dy,b,v,amp,sm,cp,cm,3);return o
    tick=time.monotonic()
    for i in range(start,nt+1):
        T=T0+i*dt
        if i in (nt-1,nt):walls[i-nt+1]=x[0,:,0,:].copy()
        k=rhs(x,T)
        if i in (nt-1,nt):walls[i-nt+3]=k[0,:,0,:].copy()
        x1=x+dt*k;x2=.75*x+.25*(x1+dt*rhs(x1,T+dt));x=(x+2*(x2+dt*rhs(x2,T+dt/2)))/3
        if (i+1)%32==0 or i==nt or time.monotonic()-tick>=budget:
            ck.save(i+1,*x,*walls)
            if i<nt and time.monotonic()-tick>=budget:print('checkpoint',i+1,'/',nt+1,flush=True);return False
    mr=receiver(x,walls,fc,sm)
    out={}
    for pos,label in enumerate(('near','far')):
        out[label]={}
        for key in ('mode_values','mode_E4','mode_E5','mode_E4_tangent','mode_E5_tangent','mode_Delta3H'):
            c,i,m,f=(np.array(z[pos][key]) for z in (cr,ir,mr,fr))
            source=m-f;prop=i-m;read=c-i;total=c-f
            np.testing.assert_allclose(source+prop+read,total,atol=1e-12,rtol=1e-12)
            out[label][key]=dict(source=source.tolist(),transport=prop.tolist(),receiver=read.tolist(),total=total.tolist())
    (work/'LVII.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out['near'],indent=2),flush=True);return True

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('work',type=Path);p.add_argument('--budget',type=float,default=12);a=p.parse_args();raise SystemExit(0 if run(a.work,a.budget) else 75)
