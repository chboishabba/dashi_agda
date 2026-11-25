"""Original two-mode replay, exact source-pulse and fixed-window slab welds."""
from check_f8_local_dual_weld import *
from check_f8_combined_residual import enclose
from run_f8_streaming_residual import clock,pulse,T0,span,R,Y,eps,stage,weights,jets,digest
from numpy.polynomial.legendre import leggauss
import math,time

def run():
    n=2;ny=225;dy=Y/(ny-1);nt=math.ceil(span/.0006);h=span/nt;k=np.arange(1,n+1)*np.pi/R;lam=k*k
    x,w=leggauss(512);r=eps*(1+x)/2;src=math.sqrt(2/R)*eps**4*(np.sin(k[:,None]*r)@(w*r*np.exp(1-1/(1-(r/eps)**2))*eps/2))
    X=np.zeros((6,ny,n));out,A,D=[np.empty_like(X) for _ in range(3)];res=[];start=time.monotonic()
    for i in range(nt+1):
        T=T0+i*h
        for q,(inp,dst,t) in enumerate(((X,A,T),(A,D,T+h),(D,out,T+h/2))):
            b,v,s,a=clock(t);amp=pulse(t)[0];z,lo,hi,*_=weights(b,dy,ny);stage(inp,X,dst,h,q,dy,v,amp,src,lam,z,lo,hi)
        if i in (50,4300):
            b0,b1=clock(T)[0],clock(T+h)[0];t0=i*Q(h);t1=(i+1)*Q(h)
            box=clock_box(t0,t1,Q(math.floor(b1*10**10)-2,10**10),Q(math.ceil(b0*10**10)+2,10**10));l=jets(X,clock(T)[1],dy);r=jets(out,clock(T+h)[1],dy)
            for j in range(n):
                kk=I(Q(j+1)*Q(333,106)/Q('3.012'),Q(j+1)*Q(355,113)/Q('3.012'));K=kk*kk
                g,gt=source_box(box,t0,t1,j+1);assert source_coeff(j+1).contains(Q(src[j]))
                bound=enclose(l[:,:,j],r[:,:,j],h,dy,(K.l,K.h),box,(g.l,g.h),(gt.l,gt.h))
                row=dict(slab=i+1,mode=j+1,source=g.floats(),source_dt=gt.floats(),primal=list(map(float,bound)),zero_incoming_forcing=float(energy_step(0,h,kk.h,box,bound)))
                if i==4300:
                    row['receiver']=[]
                    for receiver in (0,1):
                        poly,beta,Dphi,q=dual(box,window_coordinate(t0,t1),kk,0,receiver)
                        bulk,wall=pairing(l[:,:,j],r[:,:,j],h,dy,kk,box,poly,beta,g)
                        row['receiver'].append(dict(receiver=receiver,volume=bulk.floats(),wall=wall.floats(),total=(bulk+wall).floats(),radius_per_Bplus=float(Q(h)*Dphi/kk.l)))
                res.append(row)
        X,out=out,X
    return dict(rows=res,final_state_sha=digest(X),seconds=time.monotonic()-start,scope='actual reduced replay, four slab/mode enclosures; no accumulated incoming energy or receiver certificate')
if __name__=='__main__':print(json.dumps(run(),indent=2),flush=True)
