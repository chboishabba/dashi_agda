"""Separate original-source weighted4 experiment; not native A0/A1/C0/C1 receipt."""
import argparse, hashlib, json, math, time
from pathlib import Path
import numpy as np
from ksw668_f8_tt_multipole import F
from ksw668_f8_fv_source_flux import exact_cell_averages
from ksw668_f8_signed_route_stage import step,save,load

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--route',choices=['paired','ledger'],required=True)
    p.add_argument('--checkpoint',type=Path,required=True)
    p.add_argument('--dr',type=float,default=.012)
    p.add_argument('--dy',type=float,default=.012)
    p.add_argument('--dt',type=float,default=.0012)
    p.add_argument('--final-t',type=float,default=12)
    p.add_argument('--drive',type=float,default=1)
    p.add_argument('--budget',type=float,default=75)
    a=p.parse_args()
    dr,dy,eps,pulse=a.dr,a.dy,.04,.065
    if not (2<a.final_t<=20 and 0<dr<eps/3 and 0<dy<=.03 and
            0<a.dt<min(dr*math.sqrt(3/44),dy*.45) and 0<a.budget<=90):
        raise ValueError('original parameter guard')
    T0,Tend=F(1),F(a.final_t)
    nt=math.ceil((Tend-T0)/a.dt);dt=(Tend-T0)/nt
    nr=math.ceil(3.01/dr)+1;ny=math.ceil(2.01/dy)+1
    rg=np.arange(nr)*dr;src=exact_cell_averages(eps,rg,dr)
    cp=np.zeros((3,nr));cm=cp.copy()
    for q,d in enumerate((3,7,11)):
        j=np.arange(1,nr,dtype=float);den=(j+.5)**d-(j-.5)**d
        cp[q,1:]=d*(j+.5)**(d-1)/den;cm[q,1:]=d*(j-.5)**(d-1)/den
    def coeff(T):
        t=max(1.,math.exp(T+1)/2)
        for _ in range(7):
            t-=(F(t)-T)/(math.sqrt(1+t*t)/t**2)
            if t<.5:t=.5
        v=-1/math.sqrt(1+t*t);b=1/t;q=2*(T-T0)/pulse-1
        amp=-6*a.drive*math.sqrt(1-v*v)/b*math.exp(1-1/(1-q*q)) if abs(q)<1 else 0.
        return v,b,amp
    files=['ksw668_f8_tt_multipole.py','ksw668_f8_fv_source_flux.py','ksw668_f8_weighted_normal_stage.py','ksw668_f8_signed_route_stage.py',Path(__file__).name]
    identity=dict(route=a.route,dr=dr,dy=dy,dt=dt,nt=nt,final_t=a.final_t,drive=a.drive,
                  source=hashlib.sha256(src.tobytes()).hexdigest(),
                  files={f:hashlib.sha256(Path(__file__).with_name(f).read_bytes()).hexdigest() for f in files})
    X,k=load(a.checkpoint,identity) if a.checkpoint.exists() else (np.zeros((6,3,ny,nr)),0)
    if X.shape!=(6,3,ny,nr) or k>nt or np.any(X[:,:,:,-1]):raise ValueError('checkpoint geometry mismatch')
    start=time.monotonic()
    while k<nt:
        X=step(X,T0+k*dt,dt,coeff,dr,dy,src,cp,cm,a.route);k+=1
        if not np.isfinite(X).all():raise ValueError('nonfinite state')
        if k%8==0 or k==nt or time.monotonic()-start>a.budget:save(a.checkpoint,X,k,identity)
        if time.monotonic()-start>a.budget:break
    U,P,M,R,J,K=X
    D=np.empty_like(U);D[:,0]=(U[:,1]-U[:,0])/dy;D[:,-1]=(U[:,-1]-U[:,-2])/dy
    D[:,1:-1]=(U[:,2:]-U[:,:-2])/(2*dy)
    Q=(P-M)/2-D
    err=np.max(abs(Q-R-J-K))
    scale=1+np.max(abs(Q))+np.max(abs(R))+np.max(abs(J))+np.max(abs(K))+np.max(abs(D))+np.max(abs(P))+np.max(abs(M))
    if err/scale>1e-8:raise ValueError('signed constraint ledger failed')
    result=dict(route=a.route,k=k,nt=nt,ledger_error=float(err),status='COMPLETE_EXPERIMENT_ONLY' if k==nt else 'CHECKPOINTED')
    if k==nt:
        from check_f8_p0_original_same_clock_state import cubic
        span=Tend-T0;near=math.sqrt(span*span-(1-1/a.final_t)**2)-.012
        # Far receiver selection is not authenticated native receipt; explicit grid probe.
        far=min(rg[-3],near+.1)
        result['probes']={}
        for name,r in [('near',near),('far_probe',far)]:
            ids,w=cubic(r,dr,nr)
            result['probes'][name]=dict(r=float(r),mode_H=[float((r/eps)**ell*(w@U[i,0,ids])) for i,ell in enumerate((0,2,4))])
    print(json.dumps(result))
    return 0 if k==nt else 2
if __name__=='__main__':raise SystemExit(main())
