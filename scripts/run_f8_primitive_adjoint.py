"""Original F8 reverse physical-normal primitive and two wall memories.
Smooth original window only; signed source contraction, numerical pilot.
"""
import argparse,json,math,time,hashlib,os
from pathlib import Path
import numpy as np
from scipy.integrate import quad
from numpy.polynomial.legendre import leggauss
from run_f8_bidirectional_low_dual import H,END,KDF,KF,NY,DY,T0,span,R,eps,clock,pulse,stage,weights,digest

N=4;K2=KDF*KDF

def coeffs(T,norm):
    b,v,s,a=clock(T);u=10*(T-T0-span+.15)
    f=math.exp(1-1/(1-u*u))/norm if abs(u)<1 else 0.
    beta=math.sqrt(1+b*b);J=-b*b/beta
    return (np.repeat([-b*b*beta*beta*f/4,-b*b*beta*beta*f/2],2),np.repeat([-b*b*J*f/4,-b*b*(J+2*beta)*f/2],2),np.repeat([-b*b*f/4,b*b*f/2],2))

def trace(X,v):
    P,M=X[1,0],X[2,0];W=((1+v)*P+(1-v)*M)/2;N=(P-M)/2
    return X[0,0],-(W-v*N),W,N

def rhs_mem(X,J,T,norm):
    b,v,s,a=clock(T);u=-v;w=b**-3;A2,A1,A0=coeffs(T,norm);f0,f1,W,N=trace(X,u)
    Hwall=b**3*(J[0]+s*A2);P=X[1,0];target=((1-u)*P-2*Hwall)/(1+u)
    G=((1+u)*P+(u-1)*target)/2
    F=np.stack((-s*(J[1]-A1)+2*u*a*A2+(a-3*u*u/b)*w*f1+u*K2*w*f0,K2*A0+u*K2*w*f1))
    return b,u,G,F

def step(X,J,T,norm,buf):
    A,D,out=buf;JM=[]
    for q,(inp,t) in enumerate(((X,T),(A,T-H),(D,T-H/2))):
        j=J if q==0 else JM[-1];b,u,G,F=rhs_mem(inp,j,t,norm);z,lo,hi,*_=weights(b,DY,NY)
        dst=(A,D,out)[q];stage(inp,X,dst,H,q,DY,u,1.,G,K2,z,lo,hi)
        jnew=j+H*F;JM.append(jnew if q==0 else (.75*J+.25*jnew if q==1 else (J+2*jnew)/3))
    return out,JM[-1]

def seal(meta,i,X,J,wall):return hashlib.sha256((meta+str(i)+digest(X)+digest(J)+digest(wall)).encode()).hexdigest()
def run(root,budget):
    root.mkdir(parents=True,exist_ok=True);p=root/'primitive.npz';norm=.1*quad(lambda u:math.exp(1-1/(1-u*u)),-1,1,epsabs=1e-13)[0]
    files=['run_f8_primitive_adjoint.py','run_f8_bidirectional_low_dual.py','run_f8_accumulated_interval.py','run_f8_streaming_residual.py','run_f8_common_modal_box.py','f8_fused_step.py','ksw668_f8_tt_multipole.py'];base=Path(__file__).parent
    meta=json.dumps(dict(h=H,end=END,dy=DY,norm=norm,modules={x:hashlib.sha256((base/x).read_bytes()).hexdigest() for x in files}),sort_keys=True)
    if p.exists():
        with np.load(p,allow_pickle=False) as a:
            i=int(a['cursor']);X=a['X'];J=a['J'];wall=a['wall'];assert a['meta'].item()==meta and a['seal'].item()==seal(meta,i,X,J,wall)
    else:
        i=END;X=np.zeros((6,NY,N));J=np.zeros((2,N));wall=np.zeros((END+1,6,N))
    initial=i;start=time.monotonic();buf=[np.empty_like(X) for _ in range(3)]
    while i>0:
        T=T0+i*H;out,J=step(X,J,T,norm,buf);i-=1;X,buf[2]=out,X
        b,v,s,a=clock(T-H);f0,f1,W,Nn=trace(X,-v);wall[i]=np.stack((f0,f1,W,Nn,J[0],J[1]));assert np.isfinite(X).all() and np.isfinite(J).all()
        if i%128==0 or i==0 or time.monotonic()-start>=budget:
            tmp=p.with_suffix('.tmp');sig=seal(meta,i,X,J,wall)
            with tmp.open('wb') as f:np.savez(f,meta=meta,cursor=i,X=X,J=J,wall=wall,seal=sig);f.flush();os.fsync(f.fileno())
            os.replace(tmp,p)
            with np.load(p,allow_pickle=False) as a:assert a['seal'].item()==seal(a['meta'].item(),int(a['cursor']),a['X'],a['J'],a['wall'])==sig
            if time.monotonic()-start>=budget:break
    return dict(initial=initial,cursor=i,seconds=time.monotonic()-start,sha=digest(X),wall_sha=digest(wall),max_wall=np.max(abs(wall),axis=(0,2)).tolist(),meta=json.loads(meta))

def compare(root,old):
    with np.load(root/'primitive.npz',allow_pickle=False) as f:
        assert int(f['cursor'])==0 and f['seal'].item()==seal(f['meta'].item(),0,f['X'],f['J'],f['wall']);wall=f['wall']
    oldmeta=json.loads((old/'reverse.json').read_text());oldjets=np.load(old/'dual_jets.npy',mmap_mode='r');assert digest(oldjets)==oldmeta['jets_sha']
    x,w=leggauss(512);r=eps*(1+x)/2;c=math.sqrt(2/R)*eps**4*(np.sin(KF[:,None]*r)@(w*r*np.exp(1-1/(1-(r/eps)**2))*eps/2));c=np.tile(c,2)
    t=np.arange(END+1)*H;f1=wall[:,1];j1=wall[:,5];z=oldjets[:,0,0,:];p=np.zeros_like(f1);oldp=p.copy();reconstruct=p.copy()
    for i,T in enumerate(t):
        b,v,s,a=clock(T0+T);amp,ampT=pulse(T0+T);g=amp*c;gt=ampT*c;w0=b**-3
        p[i]=-(w0*gt-3*v*w0*g/b)*f1[i]-v*g*j1[i];oldp[i]=w0*g*z[i]
    # direct derivative of primitive trace on source support, independent diagnostic of IBP
    df1=np.gradient(f1,H,axis=0,edge_order=2)
    for i,T in enumerate(t):
        b,v,s,a=clock(T0+T);g=pulse(T0+T)[0]*c;reconstruct[i]=b**-3*g*(df1[i]-v*b**3*j1[i])
    integrate=lambda a:np.trapezoid(a,dx=H,axis=0)
    ans=dict(primitive=integrate(p).tolist(),direct_old=integrate(oldp).tolist(),primitive_differentiated=integrate(reconstruct).tolist(),source_coeff=c.tolist(),scope='sampled trapezoid diagnostics; no continuum error certificate or TT attachment')
    (root/'compare.json').write_text(json.dumps(ans));return ans
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('root',type=Path);p.add_argument('--budget',type=float,default=20);p.add_argument('--compare',type=Path);a=p.parse_args();assert 0<a.budget<=75
    print(json.dumps(compare(a.root,a.compare) if a.compare else run(a.root,a.budget)),flush=True)
