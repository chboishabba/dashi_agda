"""Original F8 two-mode reverse-clock scalar adjoint and forward interval replay.
Separate from discrete VJP; reduced pilot, not TT or omitted-tail acceptance.
"""
import json, math, sys, time
from fractions import Fraction as Q
from functools import lru_cache
from pathlib import Path
import numpy as np
import sympy as S
from scipy.integrate import quad
from numpy.polynomial.legendre import leggauss
import check_f8_vector_interval as vi
from check_f8_local_dual_weld import I,bjets,bump,const,add,mul,scale,neg,der,inv,sqrtj,source_box,window_coordinate,source_coeff
from check_f8_combined_residual import clock_box
from check_f8_sharp_energy import rate
from run_f8_accumulated_interval import H,END,K,KV,KF,NY,DY
from run_f8_streaming_residual import clock,pulse,T0,span,R,eps,stage,weights,jets,digest

BS=8
KD=vi.stack([vi.from_i(k) for k in K+K]);KDF=np.tile(KF,2)

@lru_cache(None)
def box_at(i):
    t0=i*Q(H);t1=min(i+BS,END)*Q(H)
    b0,b1=clock(T0+float(t0))[0],clock(T0+float(t1))[0]
    box=clock_box(t0,t1,Q(math.floor(b1*10**10)-2,10**10),Q(math.ceil(b0*10**10)+2,10**10))
    src=[source_box(box,t0,t1,n) for n in (1,2)]
    g=vi.stack([vi.from_i(x[0]) for x in src]);gt=vi.stack([vi.from_i(x[1]) for x in src])
    u=window_coordinate(t0,t1);qf=[];qft=[];q=[]
    if u.h<=-1 or u.l>=1:
        q=qf=qft=[vi.V(0)]*4
    else:
        n=4;b=bjets(I(*box[0]),n);b2=mul(b,b);beta=sqrtj(add(const(1,n),b2));J=neg(mul(b2,inv(beta)));chi=bump(u,n)
        for receiver in (0,1):
            sc,extra,sign=((Q(1,4),0,-1),(Q(1,2),2,1))[receiver]
            a2=scale(mul(mul(b2,mul(beta,beta)),chi),-sc);a1=scale(mul(mul(b2,add(J,scale(beta,extra))),chi),-sc);a0=scale(mul(b2,chi),sign*sc)
            for k in K:
                qq=add(add(der(der(a2)),neg(der(a1))),scale(a0,-k*k));flux=mul(mul(b,b2),qq)
                q.append(vi.from_i(qq[0]));qf.append(vi.from_i(flux[0]));qft.append(vi.from_i(flux[1]))
    rev=(box[0],(-box[1][1],-box[1][0]),box[2],box[3])
    return box,rev,g,gt,vi.stack(q),vi.stack(qf),vi.stack(qft),rate(box),rate(box,True)

def flux_builder():
    b,u,k=S.symbols('b u k',real=True);beta=S.sqrt(1+b*b);v=-b/beta;J=-b*b/beta;f=S.exp(1-1/(1-u*u))
    D=lambda a:v*S.diff(a,b)+10*S.diff(a,u)
    fs=[]
    for sc,extra,sign in ((S.Rational(1,4),0,-1),(S.Rational(1,2),2,1)):
        a2=-sc*b*b*beta**2*f;a1=-sc*b*b*(J+extra*beta)*f;a0=sign*sc*b*b*f
        fs.append(S.lambdify((b,u,k),b**3*(D(D(a2))-D(a1)-k*k*a0),'numpy',cse=True))
    norm=.1*quad(lambda u:math.exp(1-1/(1-u*u)),-1,1,epsabs=1e-13)[0]
    def flux(T):
        u=10*(T-T0-span+.15)
        if abs(u)>=1:return np.zeros(4)
        b=clock(T)[0];return np.concatenate([f(b,u,KF)/norm for f in fs])
    return flux

def energy(B,k,box,R0,G,GT,gamma):
    b,v,s,a=[vi.V.rational(*x) for x in box];vmin=vi.V(min(abs(v.l),abs(v.h)));vmax=vi.V(max(abs(v.l),abs(v.h)));d=vi.rat(Q(1,8))
    A=vi.V(G)/vmin;At=vi.V(GT)/vmin+vi.V(G)*vi.V(a.h)/vmin.square()
    F=vi.V(R0)+(d/(vi.V(b.l).square()*vi.V(b.l))).sqrt()*(vi.V(k.h)*A+At+(2*vmax+vi.V(s.h).sqrt())*2*A/d)
    den=1-vi.V(H)*vi.rat(gamma);assert den.l>0
    return ((vi.V(B)+F)/den).h

def trace(box,k):
    b=vi.V.rational(*box[0]);s=vi.V.rational(*box[2]);return (3*b.square()/k.square()+b.square()*b/(k*s.sqrt())).sqrt()

def step(X,buf,T,reverse,flux):
    A,D,out=buf;sign=-1 if reverse else 1;kk=KDF if reverse else KF
    for j,(inp,dst,t) in enumerate(((X,A,T),(A,D,T+sign*H),(D,out,T+sign*H/2))):
        b,v,s,a=clock(t);z,lo,hi,*_=weights(b,DY,NY);amp,src=flux(t);stage(inp,X,dst,H,j,DY,sign*v,amp,src,kk*kk,z,lo,hi)
    return out

def reverse_run(root):
    start=time.monotonic();flux=flux_builder();X=np.zeros((6,NY,4));buf=[np.empty_like(X) for _ in range(3)]
    states=np.lib.format.open_memmap(root/'dual_jets.npy',mode='w+',dtype='float64',shape=(END+1,4,NY,4));B=np.zeros(4);bound=np.zeros((END,4));raw=np.zeros(4)
    states[END]=jets(X,-clock(T0+END*H)[1],DY)
    for i in range(END-1,-1,-1):
        T=T0+(i+1)*H;box,rev,g,gt,q,qf,qft,gam,rgam=box_at(i//BS*BS)
        out=step(X,buf,T,True,lambda t:(1.,flux(t)));states[i]=jets(out,-clock(T-H)[1],DY)
        R0,G,GT,*_=vi.primal(states[i+1],states[i],H,DY,KD,rev,qf,-qft)
        B=energy(B,KD,rev,R0,G,GT,rgam);bound[i]=B;raw=vi.up(raw+R0)
        X,buf[2]=out,X
        if i%1000==0:print('reverse',i,'B',B.tolist(),flush=True)
    states.flush();np.save(root/'dual_bounds.npy',bound)
    result=dict(seconds=time.monotonic()-start,reverse_final=B.tolist(),reverse_residual=raw.tolist(),state_sha=digest(X),jets_sha=digest(states),bounds_sha=digest(bound));(root/'reverse.json').write_text(json.dumps(result));return result

def forward_run(root):
    start=time.monotonic();states=np.load(root/'dual_jets.npy',mmap_mode='r');bound=np.load(root/'dual_bounds.npy');meta=json.loads((root/'reverse.json').read_text());assert digest(states)==meta['jets_sha'] and digest(bound)==meta['bounds_sha']
    x,w=leggauss(512);r=eps*(1+x)/2;src=math.sqrt(2/R)*eps**4*(np.sin(KF[:,None]*r)@(w*r*np.exp(1-1/(1-(r/eps)**2))*eps/2));assert all(source_coeff(n).contains(Q(src[n-1])) for n in (1,2))
    X=np.zeros((6,NY,2));buf=[np.empty_like(X) for _ in range(3)];B=np.zeros(2);tot=vi.V(np.zeros(4));walltot=vi.V(np.zeros(4));rem=np.zeros(4);tr=np.zeros(4);obs=vi.V(np.zeros(4));res=np.zeros(2)
    for i in range(END):
        T=T0+i*H;box,rev,g,gt,q,qf,qft,gam,rgam=box_at(i//BS*BS)
        l=jets(X,clock(T)[1],DY);out=step(X,buf,T,False,lambda t:(pulse(t)[0],src));rj=jets(out,clock(T+H)[1],DY)
        R0,G,GT,r,gerr,w,wall=vi.primal(l,rj,H,DY,KV,box,g,gt);B=energy(B,KV,box,R0,G,GT,gam);res=vi.up(res+R0)
        c=vi.bezier(states[i+1],states[i],H,DY);p=c.hull((0,1));p0=c[:,0,0,:].hull(0)
        def tile(v):return vi.V(np.tile(v.l,(1,2)) if v.l.ndim==2 else np.tile(v.l,2),np.tile(v.h,(1,2)) if v.h.ndim==2 else np.tile(v.h,2))
        tot=tot+(tile(r)*w*p*DY*H).sum(0);b=vi.V.rational(*box[0]);w0=1/(b.square()*b);walltot=walltot+tile(gerr)*p0*w0*H
        C=trace(box,KD);D=vi.V(bound[i]);rem=(vi.V(rem)+D/vi.V(KD.l)*vi.V(np.tile(R0,2))+w0*C*D*vi.V(np.tile(G,2))).h
        tr=(vi.V(tr)+vi.V(np.tile(B,2))*C*vi.V(q.mag())*H).h;obs=obs+q*tile(wall)*H
        X,buf[2]=out,X
        if (i+1)%1000==0:print('forward',i+1,'B',B.tolist(),'rem',rem.tolist(),flush=True)
    result=dict(seconds=time.monotonic()-start,forward_final=B.tolist(),residual=res.tolist(),state_sha=digest(X),bulk=[tot.l.tolist(),tot.h.tolist()],wall=[walltot.l.tolist(),walltot.h.tolist()],remainder=rem.tolist(),trace=tr.tolist(),observation=[obs.l.tolist(),obs.h.tolist()],scope='conditional scalar modes 1,2 both E4/SMS; no TT or omitted tail')
    (root/'forward.json').write_text(json.dumps(result));return result

if __name__=='__main__':
    root=Path(sys.argv[2]);root.mkdir(parents=True,exist_ok=True);print(json.dumps(reverse_run(root) if sys.argv[1]=='reverse' else forward_run(root)),flush=True)
