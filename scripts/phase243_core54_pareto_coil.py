from __future__ import annotations
from itertools import product
import numpy as np

F3=(0,1,2)
PAIR={0:(1,2),1:(3,4),2:(5,6),3:(7,8)}
PHASE={0:0.0,1:2*np.pi/3,2:4*np.pi/3}
R0,A0,IOTA0=3.0,1.0,0.42

def _dd(f,a,h): return (np.roll(f,-1,axis=a)-np.roll(f,1,axis=a))/(2*h)
def _other(m): return tuple(x for x in F3 if x!=m)
def _planes(k,u,v):
    if k==0: return (u,0),(u,v+1)
    if k==1:
        h1,h2=_other(v); return (u,h1+1),(u,h2+1)
    c1,c2=_other(u); return (c1,v+1),(c2,v+1)

def _grid(nth=9,nz=12):
    th=np.linspace(0,2*np.pi,nth,endpoint=False); ze=np.linspace(0,2*np.pi,nz,endpoint=False)
    TH,ZE=np.meshgrid(th,ze,indexing='ij'); dt,dz=2*np.pi/nth,2*np.pi/nz
    B=np.stack([np.ones_like(TH),np.cos(TH),np.sin(TH),np.cos(3*ZE),np.sin(3*ZE),np.cos(TH-3*ZE),np.sin(TH-3*ZE),np.cos(TH+3*ZE),np.sin(TH+3*ZE)],-1)
    Bt=np.stack([np.zeros_like(TH),-np.sin(TH),np.cos(TH),np.zeros_like(TH),np.zeros_like(TH),-np.sin(TH-3*ZE),np.cos(TH-3*ZE),-np.sin(TH+3*ZE),np.cos(TH+3*ZE)],-1)
    Bz=np.stack([np.zeros_like(TH),np.zeros_like(TH),np.zeros_like(TH),-3*np.sin(3*ZE),3*np.cos(3*ZE),3*np.sin(TH-3*ZE),-3*np.cos(TH-3*ZE),-3*np.sin(TH+3*ZE),3*np.cos(TH+3*ZE)],-1)
    return TH,ZE,dt,dz,B,Bt,Bz

def _dir(plane,phase):
    ch,h=plane; c=np.zeros(27); i,j=PAIR[h]; a=PHASE[phase]; off=9*ch
    c[off+i]=np.cos(a); c[off+j]=np.sin(a); return c

def _geom(c, grid=None):
    TH,ZE,dt,dz,B,Bt,Bz = _grid() if grid is None else grid
    cr,cz,cs=c[:9],c[9:18],c[18:]
    rho=A0*(1+np.tensordot(B,cr,axes=([-1],[0]))); zoff=A0*np.tensordot(B,cz,axes=([-1],[0]))
    RR=R0+rho*np.cos(TH); ZZ=rho*np.sin(TH)+zoff
    r=np.stack([RR*np.cos(ZE),RR*np.sin(ZE),ZZ],-1)
    e1,e2=_dd(r,0,dt),_dd(r,1,dz); cross=np.cross(e1,e2); sg=np.linalg.norm(cross,axis=-1); n=cross/sg[...,None]
    ct=1+np.tensordot(Bt,cs,axes=([-1],[0])); czeta=-IOTA0+np.tensordot(Bz,cs,axes=([-1],[0]))
    bth,bze=czeta/sg,-ct/sg; bv=bth[...,None]*e1+bze[...,None]*e2; bm=np.linalg.norm(bv,axis=-1); bh=bv/bm[...,None]
    kap=(bth/bm)[...,None]*_dd(bh,0,dt)+(bze/bm)[...,None]*_dd(bh,1,dz); q=np.cross(n,bh); q/=np.linalg.norm(q,axis=-1)[...,None]
    kg=np.sum(kap*q,axis=-1); div=(_dd(sg*bth,0,dt)+_dd(sg*bze,1,dz))/sg
    return {'r':r,'normal':n,'Brel':float(np.std(bm)/np.mean(bm)),'kg':float(np.sqrt(np.mean(kg*kg))),'div':float(np.sqrt(np.mean(div*div))),'minrho':float(np.min(rho)),'norm':float(np.linalg.norm(c))}

def _solve_geom(tag,delta,floor=.04,grid=None):
    k,u,v,rel=tag; p,q=(0,0) if rel==0 else (0,1); pl1,pl2=_planes(k,u,v); d1,d2=_dir(pl1,p),_dir(pl2,q)
    mask=np.array([pl1[1]!=0,pl2[1]!=0],float); amps=(-.16,-.10,-.06,-.04,.04,.06,.10,.16); best=None
    for a in amps:
        for b in amps:
            na=float(np.linalg.norm(np.array([a,b])*mask))
            if na+1e-12<floor: continue
            c=a*d1+b*d2; m=_geom(c,grid)
            obj=20*m['Brel']**2+(0.5+4*delta)*m['kg']**2+50*m['div']**2+0.02*m['norm']**2
            rec=(obj,np.array([a,b]),c,m,na)
            if best is None or obj<best[0]: best=rec
    return best

def _dominates(a,b):
    axes=('Brel','kg','flow','anisotropy','geometry_burden','complexity')
    return all(a[x]<=b[x]+1e-12 for x in axes) and any(a[x]<b[x]-1e-12 for x in axes)

def _pareto(xs): return [x for i,x in enumerate(xs) if not any(j!=i and _dominates(y,x) for j,y in enumerate(xs))]

def _coil_inverse(c):
    g=_grid(7,9); pm=_geom(c,g); rp=pm['r']; npn=pm['normal']; TH,ZE,dt,dz,*_=g
    Rxy=np.sqrt(rp[...,0]**2+rp[...,1]**2); phi=np.arctan2(rp[...,1],rp[...,0]); Zp=rp[...,2]
    Rw=R0+1.28*(Rxy-R0); Zw=1.28*Zp; rw=np.stack([Rw*np.cos(phi),Rw*np.sin(phi),Zw],-1)
    rwt,rwz=_dd(rw,0,dt),_dd(rw,1,dz); cr=np.cross(rwt,rwz); jw=np.linalg.norm(cr,axis=-1); nw=cr/jw[...,None]
    gtt=np.sum(rwt*rwt,-1); gtz=np.sum(rwt*rwz,-1); gzz=np.sum(rwz*rwz,-1); det=gtt*gzz-gtz*gtz
    gi_tt,gi_tz,gi_zz=gzz/det,-gtz/det,gtt/det
    modes=[]
    for m in (0,1,2):
        for n in (1,2): modes += [('c',m,n),('s',m,n)]
    for m in (1,2,3): modes += [('c',m,0),('s',m,0)]
    def K(mode):
        typ,m,n=mode; arg=m*TH-3*n*ZE
        if typ=='c': pt=-m*np.sin(arg); pz=3*n*np.sin(arg)
        else: pt=m*np.cos(arg); pz=-3*n*np.cos(arg)
        at=gi_tt*pt+gi_tz*pz; az=gi_tz*pt+gi_zz*pz; grad=at[...,None]*rwt+az[...,None]*rwz
        return np.cross(nw,grad)
    R=np.sqrt(rp[...,0]**2+rp[...,1]**2); ephi=np.stack([-rp[...,1]/R,rp[...,0]/R,np.zeros_like(R)],-1); Bbase=(R0/R)[...,None]*ephi
    target=-np.sum(Bbase*npn,-1).reshape(-1); P=rp.reshape(-1,3); PN=npn.reshape(-1,3); W=rw.reshape(-1,3); area=(jw*dt*dz).reshape(-1)
    A=np.zeros((P.shape[0],len(modes))); soft=.05**2
    for j,mode in enumerate(modes):
        kk=K(mode).reshape(-1,3); dr=P[:,None,:]-W[None,:,:]; r2=np.sum(dr*dr,-1)+soft
        dB=np.cross(kk[None,:,:],dr)*area[None,:,None]/(r2**1.5)[...,None]; BB=np.sum(dB,1); A[:,j]=np.sum(BB*PN,-1)
    best=None
    for lam in np.logspace(-7,-2,8):
        x=np.linalg.solve(A.T@A+lam*np.eye(A.shape[1]),A.T@target); pred=A@x
        rel=float(np.sqrt(np.mean((pred-target)**2))/(np.sqrt(np.mean(target**2))+1e-15)); norm=float(np.linalg.norm(x)); merit=rel+0.003*norm
        if best is None or merit<best[0]: best=(merit,rel,norm)
    return {'coil_relative_bn_residual':best[1],'coil_coefficient_norm':best[2]}

def solve_maxcut(nonaxis_floor=.04,coil_limit=6):
    grid=_grid(); reps=list(product(F3,F3,F3,(0,1))); records=[]
    for tag in reps:
        for delta in (0.0,.25,.5,.75,1.0):
            sol=_solve_geom(tag,delta,nonaxis_floor,grid)
            if sol is None: continue
            _,x,c,m,na=sol
            for share in (.25,.5,.75):
                rem=1-delta; M2=share*rem; alpha=(1-share)*rem
                records.append({'tag':tag,'a1':float(x[0]),'a2':float(x[1]),'nonaxis_norm':na,'deltaC':delta,'M':float(np.sqrt(M2)),'alpha':float(alpha),'Brel':m['Brel'],'kg':m['kg'],'div_rms':m['div'],'minrho':m['minrho'],'flow':float(M2),'anisotropy':float(alpha),'geometry_burden':float(delta),'complexity':m['norm'],'coeff':c})
    p=_pareto(records); axes=('Brel','kg','flow','anisotropy','geometry_burden','complexity')
    mins={a:min(x[a] for x in p) for a in axes}; maxs={a:max(x[a] for x in p) for a in axes}
    def compromise(x): return sum((x[a]-mins[a])/(maxs[a]-mins[a]+1e-12) for a in axes)
    coils=[]; seen=set()
    for x in sorted(p,key=compromise):
        key=(x['tag'],round(x['deltaC'],3),round(x['a1'],4),round(x['a2'],4))
        if key in seen: continue
        seen.add(key); y=dict(x); y.update(_coil_inverse(x['coeff'])); y.pop('coeff',None); coils.append(y)
        if len(coils)>=coil_limit: break
    pout=[]
    for x in p:
        y=dict(x); y.pop('coeff',None); pout.append(y)
    return {'representative_count':54,'record_count':len(records),'pareto_count':len(pout),'pareto':pout,'coil_survivor_count':sum(x['coil_relative_bn_residual']<1 for x in coils),'coil_survivors':coils}

if __name__=='__main__':
    r=solve_maxcut(); print({k:v for k,v in r.items() if k not in ('pareto','coil_survivors')}); print('coils',r['coil_survivors'])
