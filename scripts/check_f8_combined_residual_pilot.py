from check_f8_combined_residual import *
from run_f8_streaming_residual import clock,pulse,T0,span,R,Y,eps,stage,weights,jets,digest
from numpy.polynomial.legendre import leggauss
import math,time
n=2;ny=225;dy=Y/(ny-1);nt=math.ceil(span/.0006);h=span/nt;k=np.arange(1,n+1)*np.pi/R;lam=k*k
x,w=leggauss(512);r=eps*(1+x)/2;src=math.sqrt(2/R)*eps**4*(np.sin(k[:,None]*r)@(w*r*np.exp(1-1/(1-(r/eps)**2))*eps/2))
X=np.zeros((6,ny,n));out,A,D=[np.empty_like(X) for _ in range(3)];res=[];start=time.monotonic()
for i in range(nt+1):
    T=T0+i*h
    for q,(inp,dst,t) in enumerate(((X,A,T),(A,D,T+h),(D,out,T+h/2))):
        b,v,s,a=clock(t);amp=pulse(t)[0];z,lo,hi,*_=weights(b,dy,ny);stage(inp,X,dst,h,q,dy,v,amp,src,lam,z,lo,hi)
    if i in (110,511,4300):
        b0,b1=clock(T)[0],clock(T+h)[0];blo=Q(math.floor(b1*10**10)-2,10**10);bhi=Q(math.ceil(b0*10**10)+2,10**10)
        box=clock_box(i*Q(h),(i+1)*Q(h),blo,bhi);l=jets(X,clock(T)[1],dy);r=jets(out,clock(T+h)[1],dy)
        for j in range(n):
            kl=Q(j+1)*Q(333,106)/Q('3.012');kh=Q(j+1)*Q(355,113)/Q('3.012');sa=12*Q('0.04')**6 if i*h<.065 else Q(0);st=10000*Q('0.04')**6 if i*h<.065 else Q(0)
            new=enclose(l[:,:,j],r[:,:,j],h,dy,(kl*kl,kh*kh),box,(-sa,sa),(-st,st));old=exact_majorant(l[:,:,j],r[:,:,j],h,dy,kh*kh,(blo,-box[1][0],box[2][1],box[3][1]),sa,st)
            res.append(dict(slab=i+1,mode=j+1,old=list(map(float,old)),combined=list(map(float,new)),energy_zero_input=float(energy_step(0,h,kh,box,new)),ratio=[float(a/b) if b else None for a,b in zip(old,new)]))
    X,out=out,X
print(json.dumps(dict(rows=res,final_state_sha=digest(X),seconds=time.monotonic()-start)),flush=True)
