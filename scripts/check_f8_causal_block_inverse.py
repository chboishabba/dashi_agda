"""Whole-slab forward scalar Volterra certificate, deliberately coarse.
Positive characteristic flux + residual of literal bilinear candidate; causal
block propagation, no global contraction. Conditional IEEE basic arithmetic.
"""
import json, math, sys, time
from decimal import Decimal, localcontext, ROUND_CEILING
from fractions import Fraction as Q
import numpy as np
from scipy.linalg import solve_triangular
from check_f8_global_wall_kernel import clock,grid,interp,Fbox
from check_f8_kernel_hermite_residual import I,iv,rat,D,U,prefix,pi_box

def sqrt(a):
    return I(D(np.sqrt(np.maximum(0,a.l))),U(np.sqrt(np.maximum(0,a.h))))
def hull(a,b):return I(np.minimum(a.l,b.l),np.maximum(a.h,b.h))
def intersect(a,b):
    lo=np.maximum(a.l,b.l);hi=np.minimum(a.h,b.h);assert np.all(lo<=hi);return I(lo,hi)
def box(x):return I(x[0],x[1])
def absup(a):return I(a.mag())
def isum(a):
    l,h=a.l,a.h
    if not len(l):return I(0)
    while len(l)>1:
        n=len(l)//2;ll=D(l[:2*n:2]+l[1:2*n:2]);hh=U(h[:2*n:2]+h[1:2*n:2])
        l=np.r_[ll,l[-1:]] if len(l)%2 else ll;h=np.r_[hh,h[-1:]] if len(h)%2 else hh
    return I(l[0],h[0])
def qsum(a):
    a=list(a);return isum(I([x.l for x in a],[x.h for x in a]))

def envelope(r,xi,k2,h):
    # Residual valid uniformly for every source xi in its whole slab.
    a,b,c,d=r[:-1,:-1],r[1:,:-1],r[:-1,1:],r[1:,1:]
    z=xi+I((np.arange(a.shape[0])[:,None]-np.arange(a.shape[1])[None,:])*h/2)+I(-h/2,h/2)
    cut=rat(Q(1,13));zl=np.maximum(z.l,cut.l);zh=np.maximum(z.h,cut.h)
    V=k2+rat(Q(15,4))/(I(zl,zh)*I(zl,zh))
    mixed=(I(d)-I(b)-I(c)+I(a))*4/(h*h)
    Rh=I(np.minimum(np.minimum(a,b),np.minimum(c,d)),np.maximum(np.maximum(a,b),np.maximum(c,d)))
    f=(mixed+V*Rh).mag();q=prefix(U(U(f*f)*h*h))
    return f,V.h,q

def flux_energy(A,B,xi,k2):
    # R(A,0)=R(0,B)=1. Positive energy flux across rectangle.
    # Integrate potential along axes using monotonic endpoint rectangles (16 panels).
    cut=rat(Q(1,13));
    def v(z):
        z=I(np.maximum(z.l,cut.l),np.maximum(z.h,cut.h));return k2+rat(Q(15,4))/(z*z)
    def integ(length,sign,origin):
        j=np.arange(16);z=origin+I(j,j+1)*(length/32)*sign
        a=v(z);return U(isum(I(a.h)).h*length.h/16)
    av,bv=A.h,B.h
    S=U(integ(I(av),1,xi)+integ(I(bv),-1,xi))
    radius=U(.5*U(np.sqrt(U(min(av,bv)*S))))
    VA=integ(I(bv),-1,xi+I(A.l,A.h)/2);VB=integ(I(av),1,xi-I(B.l,B.h)/2)
    ra=U(.25*U(np.sqrt(U(VA*S))));rb=U(.25*U(np.sqrt(U(VB*S))))
    return I(D((1-radius)/2),U((1+radius)/2)),I(-U((ra+rb)/2),U((ra+rb)/2)),I(-U((ra+rb)/2),U((ra+rb)/2))

def enclose(r,f,V,q,xi,k2,h,A,B):
    ai=max(0,int(np.floor(A.l/h)));aj=int(np.floor(A.h/h));bi=max(0,int(np.floor(B.l/h)));bj=int(np.floor(B.h/h));assert aj<f.shape[0] and bj<f.shape[1]
    F2=q[aj,bj];T=U(U(A.h+B.h)/2);E=U(T*U(np.sqrt(U(F2/2))))
    # Forced rectangle flux <= T F2/2. Thus int V e^2 on each
    # outgoing characteristic <= T F2, and derivative via Cauchy-Schwarz.
    def der(f,V):
        l=len(f)*h;ff=(isum(I(f))*h).h;vv=(isum(I(V))*h).h
        return U((I(ff)+sqrt(I(vv)*I(T)*I(F2))).h/4)
    ea=der(np.max(f[ai:aj+1,:bj+1],axis=0),np.max(V[ai:aj+1,:bj+1],axis=0));eb=der(np.max(f[:aj+1,bi:bj+1],axis=1),np.max(V[:aj+1,bi:bj+1],axis=1))
    block=r[ai:aj+2,bi:bj+2];da=(I(block[1:])-I(block[:-1]))/h;db=(I(block[:,1:])-I(block[:,:-1]))/h
    da=I(D(np.min(da.l)-ea),U(np.max(da.h)+ea));db=I(D(np.min(db.l)-eb),U(np.max(db.h)+eb))
    values=(I(D(np.min(block)-E),U(np.max(block)+E))/2,(da+db)/2,(da-db)/2)
    # independent positive homogeneous flux and local signed Picard bounds
    caps=flux_energy(A,B,xi,k2);values=tuple(intersect(a,b) for a,b in zip(values,caps))
    M=np.max(V[:aj+1,:bj+1]);x=(I(M)*I(A.h)*I(B.h)/4).h
    if x<.5:
        tail=(I(x)/(1-I(x))).h;cap=I(D((1-tail)/2),U((1+tail)/2));fac=(I(M)/(4*(1-I(x)))).h
        # R positive on whole rectangle. Both characteristic derivatives nonpositive.
        ra=I(-U(fac*B.h),0);rb=I(-U(fac*A.h),0)
        values=tuple(intersect(a,b) for a,b in zip(values,(cap,(ra+rb)/2,(ra-rb)/2)))
    return values

def kernel_pairs(n,mode,dt,b,lo,hi,h):
    # b arrays in forward order, intervals include both original endpoints.
    pl,ph=pi_box();k=I(D(float(mode*pl/Q('3.012'))),U(float(mode*ph/Q('3.012'))));k2=k*k
    bs=[I(lo[j+1],hi[j]) for j in range(n)];vals=np.zeros((n,n,3,2));p=np.zeros((n,n,3));kfloat=mode*np.pi/3.012
    for j,xi in enumerate(bs):
        boxes=[]
        for i,z in enumerate(bs):
            lag=I(max(0,abs(i-j)-1),abs(i-j)+1)*dt;dz=z-xi
            A=lag+dz;B=lag-dz;A=I(max(0,A.l),A.h);B=I(max(0,B.l),B.h);boxes.append((A,B))
        na=int(max(a.h for a,bx in boxes)/h)+2;nb=int(max(bx.h for a,bx in boxes)/h)+2
        center=float((xi.l+xi.h)/2);r=grid(center,kfloat,h,na,nb);f,V,q=envelope(r,xi,k2,h)
        for i,(A,B) in enumerate(boxes):
            v=enclose(r,f,V,q,xi,k2,h,A,B);vals[i,j]=[[x.l,x.h] for x in v]
            dz=b[i+1]-b[j+1];lag=abs(i-j)*dt
            if i!=j:p[i,j]=np.array(interp(r,np.array([lag+dz]),np.array([lag-dz]),h)).ravel()
            else:p[i,j]=[.5,0,0]
    return vals,p,bs,k,k2

def bumpjet(u):
    # For x=1/(1-u²), x^j exp(1-x) is unimodal, max at x=j.
    u=I(max(-1,u.l),min(1,u.h));
    if u.l>=u.h:return I(0),I(0),I(0)
    amin=0 if u.l<=0<=u.h else min(abs(u.l),abs(u.h));amax=max(abs(u.l),abs(u.h));xl=max(1,float((I(1)/(1-I(amin)*I(amin))).l));xh=np.inf if amax>=1 else float((I(1)/(1-I(amax)*I(amax))).h)
    def point(x,j):
        if np.isinf(x):return I(0)
        # Decimal exp correctly rounded; padded before binary64 conversion.
        with localcontext() as c:
            c.prec=60;a=Decimal.from_float(float(x));e=(1-a).exp();v=e*(a**j);y=float(v)
            return I(max(0,D(D(y))),U(U(y)))
    def term(j):
        a=point(xl,j);b=point(xh,j);m=point(float(j),j) if xl<=j<=xh else I(0);return I(min(a.l,b.l),max(a.h,b.h,m.h))
    p=term(0);p1=-2*u*term(2);p2=-2*term(2)-8*u*u*term(3)+4*u*u*term(4)
    return p,p1,p2

def data(bs,k,k2,dt,spanbox,n):
    # Padded clock starts earlier than original t=1; exact original source shift.
    total=Q(float(dt))*n;pad=I(D(float(total-spanbox[1])),U(float(total-spanbox[0])))
    eps=rat(Q(1,25));coefhi=(sqrt(I(2)/rat(Q('3.012')))*eps*eps*eps*eps*k*eps*eps*eps/3).h
    # Positive source coefficient: sine positive for k eps < pi; no need guessed lower bound.
    coef=I(0,coefhi);src=[];obs=[[],[]]
    for i,b in enumerate(bs):
        time=I(i,i+1)*dt;elapsed=time-pad;v=-b/sqrt(1+b*b);a=b/((1+b*b)*(1+b*b));beta=sqrt(1+b*b)
        if elapsed.h<=0 or elapsed.l>=rat(Q(13,200)).h:gg=I(0)
        else:
            u=elapsed*rat(Q(400,13))-1;f,_,_=bumpjet(u);gg=-6*coef*f/(b*beta*b*sqrt(b))
        src.append(gg)
        u=(time-rat(total)+rat(Q(3,20)))*10
        if u.h<=-1 or u.l>=1:
            for row in obs:row.append(I(0))
            continue
        chi,ch1,ch2=bumpjet(u);norm=I(D(1/15),U(1/5));chi=chi/norm;ch1=10*ch1/norm;ch2=100*ch2/norm
        p=b*b*(1+b*b);p1=(2*b+4*b*b*b)*v;p2=(2+12*b*b)*v*v+(2*b+4*b*b*b)*a
        for row,(sc,extra,sign) in zip(obs,((.25,0,-1),(.5,2,1))):
            r=-b*b*b*b/beta+extra*b*b*beta;rp=(-4*b*b*b/beta+b*b*b*b*b/(beta*beta*beta)+extra*(2*b*beta+b*b*b/beta))*v
            q=-sc*(p2*chi+2*p1*ch1+p*ch2)+sc*(rp*chi+r*ch1)-k2*sign*sc*b*b*chi
            row.append(q*b*sqrt(b))
    return src,obs,float(coefhi)

def propagate(H,d):
    # Decimal ceiling for arbitrary-range positive bounds; exact input floats.
    with localcontext() as c:
        c.prec=40;c.rounding=ROUND_CEILING;e=[]
        for i in range(len(d)):
            den=Decimal(1)-Decimal.from_float(float(H[i,i]));assert den>0
            # subtraction rounded downward: exact dyadic den converted via floor of binary operation
            den=Decimal.from_float(float(D(1-H[i,i])));assert den>0
            num=Decimal.from_float(float(d[i]))+sum((Decimal.from_float(float(H[i,j]))*e[j] for j in range(i)),Decimal(0));e.append(num/den)
        return e

def run(n,mode):
    start=time.monotonic();dt,t,b,lo,hi,span=clock(n);b=b[::-1];lo=lo[::-1];hi=hi[::-1];h=1/128
    vals,p,bs,k,k2=kernel_pairs(n,mode,dt,b,lo,hi,h);print('pairs',mode,n,time.monotonic()-start,flush=True)
    a,c=Fbox(Q(1,12));l,r=Fbox(Q(1));src,obs,coef=data(bs,k,k2,dt,(a-r,c-l),n)
    L=np.zeros((n,n));Delta=np.zeros_like(L);fL=np.zeros(n);fH=np.zeros(n);widths=np.zeros(3)
    for i in range(n):
        fs=I(0)
        for j in range(i+1):
            K=intersect(box(vals[i,j,0]),box(vals[j,i,0]));Kt=intersect(box(vals[i,j,1]),box(vals[j,i,1]));Kx=box(vals[j,i,2]);v=-bs[j]/sqrt(1+bs[j]*bs[j]);ell=2*(Kx-v*Kt+1.5*K/bs[j]);widths=np.maximum(widths,[K.h-K.l,Kt.h-Kt.l,Kx.h-Kx.l]);
            if j<i:
                vb=-b[j+1]/np.sqrt(1+b[j+1]**2);L[i,j]=float(2*(p[j,i,2]-vb*p[i,j,1]+1.5*p[i,j,0]/b[j+1])*dt)
                Delta[i,j]=(ell*dt-I(L[i,j])).mag()
            else:
                # On causal diagonal A+B<=2dt, AB<=dt². Sharper local bound.
                cut=rat(Q(1,13));zmin=max(cut.l,(bs[j]-I(dt)/2).l);M=(k2+rat(Q(15,4))/(I(zmin)*I(zmin))).h
                y=(I(M)*I(dt)*I(dt)/4).h
                if y<.5:
                    kk=(I(1)/(2*(1-I(y)))).h;der=(I(M)*I(dt)/(4*(1-I(y)))).h
                    local=(2*(I(der)*(1+absup(v))+1.5*I(kk)/bs[j])*dt).h
                    Delta[i,j]=min((absup(ell)*dt).h,local)
                else:Delta[i,j]=(absup(ell)*dt).h
            term=-2*K*src[j]*dt
            fs=fs+(hull(I(0),term) if j==i else term)
        fL[i],fH[i]=fs.l,fs.h
    print("diagonal",np.max(np.diag(Delta)),flush=True);assert np.max(np.diag(Delta))<1
    # Signed finite inverse of exact literal strict lower L, then absolute block norms.
    A=np.eye(n)-L;G=solve_triangular(A,np.eye(n),lower=True);C=G-np.eye(n);assert np.all(np.diag(G)==1) and np.all(np.triu(G,1)==0)
    # Explicit outward interval residual and finite inverse correction, no BLAS error model.
    err=np.zeros_like(G)
    for i in range(n):
        for j in range(i):
            z=I(G[i,j])-isum(I(L[i,j:i])*I(G[j:i,j]))
            err[i,j]=z.mag()
    rho=max(isum(I(row)).h for row in err);gn=max(isum(I(abs(row))).h for row in G);assert rho<1
    corr=(I(gn)*I(rho)/(1-I(rho))).h
    P=np.tril(U(abs(C)+corr),-1)+np.eye(n)
    H=np.zeros_like(L)
    for i in range(n):
        for j in range(i+1):H[i,j]=isum(I(P[i,j:i+1])*I(Delta[j:i+1,j])).h
    fhat=(fL+fH)/2;x=solve_triangular(A,fhat,lower=True);r0=[]
    for i in range(n):
        z=I(x[i])-I(fL[i],fH[i]);
        z=z-isum(I(L[i,:i])*I(x[:i]))
        r0.append((I(z.mag())+isum(I(Delta[i,:i+1])*I(abs(x[:i+1])))).h)
    d=np.array([isum(I(P[i,:i+1])*I(r0[:i+1])).h for i in range(n)])
    pre=propagate(H,d);direct=propagate(U(Delta+abs(L)),np.array(r0));e=[min(a,b) for a,b in zip(pre,direct)]
    # Signed reconstruction observer plus absolute error, using exact original q on slabs.
    results=[]
    for row in obs:
        signed=qsum([q*I(xi)*dt for q,xi in zip(row,x)])
        with localcontext() as cc:
            cc.prec=40;cc.rounding=ROUND_CEILING;rad=sum((Decimal.from_float(float((absup(q)*dt).h))*ee for q,ee in zip(row,e)),Decimal(0));totalrad=rad+Decimal.from_float(float(signed.mag()))
        results.append(dict(reconstruction=[float(signed.l),float(signed.h)],radius=str(rad),absolute_upper=str(totalrad)))
    return dict(n=n,mode=mode,seconds=time.monotonic()-start,whole_ordered_pairs=n*n,causal_pairs=n*(n+1)//2,characteristic_h=h,source_coeff_upper=coef,kernel_max_widths=widths.tolist(),diagonal_max=float(np.max(np.diag(H))),finite_inverse_defect=float(rho),finite_inverse_correction=float(corr),global_delta_max=float(max(qsum([I(v) for v in row]).h for row in Delta)),preconditioned_global_row_max=float(max(qsum([I(v) for v in row]).h for row in H)),preconditioned_last_error=str(pre[-1]),direct_last_error=str(direct[-1]),last_error=str(e[-1]),max_error=str(max(e)),observer=results,scope='conditional whole-slab continuous scalar certificate, intentionally coarse; no TT/tail or physical acceptance')

if __name__=='__main__':print(json.dumps(run(int(sys.argv[1]),int(sys.argv[2])),indent=2),flush=True)
