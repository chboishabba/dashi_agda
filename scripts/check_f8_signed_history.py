"""Signed causal inverse before absolute enclosure; ternary history Schur recovery.
Whole-slab original F8 carrier, conditional arithmetic as in causal owner.
"""
import json, sys, time
from fractions import Fraction as Q
from decimal import Decimal, localcontext, ROUND_CEILING
import numpy as np
from scipy.linalg import solve_triangular
from check_f8_global_wall_kernel import clock,Fbox
from check_f8_causal_block_inverse import I,D,U,rat,sqrt,box,intersect,isum,qsum,absup,hull,kernel_pairs,data,propagate

def frames(n):
    # Consecutive triples, with any final short group retained exactly.
    rows=[];res=[];cols=[];rc=[]
    for j in range(0,n,3):
        m=min(3,n-j);a=np.zeros(n);a[j:j+m]=1/m;rows.append(a)
        a=np.zeros(n);a[j:j+m]=1;cols.append(a)
        for l in range(m-1):
            a=np.zeros(n);a[j+l]=1;a[j+m-1]=-1;res.append(a)
            a=np.zeros(n);a[j:j+m]=-1/m;a[j+l]+=1;rc.append(a)
    return np.array(rows),np.array(res),np.array(cols).T,np.array(rc).T

def exact():
    import sympy as S
    # exact rational coarse/fine frame for a single triple and two-cell collar
    checks=0
    for m in (2,3):
        q=S.ones(1,m)/m;j=S.ones(m,1);r=S.zeros(m-1,m);p=S.zeros(m,m-1)
        for a in range(m-1):
            r[a,a]=1;r[a,m-1]=-1
            p[:,a]=S.eye(m)[:,a]-j/m
        T=q.col_join(r);J=j.row_join(p);assert T*J==J*T==S.eye(m);checks+=1
        assert q*p==S.zeros(1,m-1) and r*j==S.zeros(m-1,1);checks+=1
        # Same average, different next-history observation: causal map with lag.
        L=S.zeros(m);L[1,0]=1;assert q*L*p!=S.zeros(1,m-1);checks+=1
        A=S.eye(m)-L;Z=T*A*J;aa=Z[:1,:1];b=Z[:1,1:];c=Z[1:,:1];d=Z[1:,1:];f=S.Matrix(range(1,m+1));ff=T*f
        x=(aa-b*d.inv()*c).inv()*(ff[:1,:]-b*d.inv()*ff[1:,:]);y=d.inv()*(ff[1:,:]-c*x);assert J*x.col_join(y)==A.inv()*f;checks+=1
    return checks

def schur(A,f,x):
    q,r,j,p=frames(len(x));a=q@A@j;b=q@A@p;c=r@A@j;d=r@A@p;fc=q@f;fr=r@f
    dc=np.linalg.solve(d,c);df=np.linalg.solve(d,fr);sc=a-b@dc;y=np.linalg.solve(sc,fc-b@df);z=df-dc@y;xx=j@y+p@z
    return dict(coarse=len(q),complement=len(r),roundtrip=float(np.max(abs(j@q+p@r-np.eye(len(x))))),recovered_error=float(np.max(abs(xx-x))),signed_feedback_norm=float(np.linalg.norm(b@dc,np.inf)),complement_source_norm=float(np.max(abs(b@df))),non_descent_norm=float(np.linalg.norm(q@(np.eye(len(x))-A)@p,np.inf)),finite_residual=float(np.max(abs(A@xx-f))))

def run(n,mode):
    start=time.monotonic();dt,t,b,lo,hi,span=clock(n);b=b[::-1];lo=lo[::-1];hi=hi[::-1]
    vals,p,bs,k,k2=kernel_pairs(n,mode,dt,b,lo,hi,1/128);print('pairs',mode,time.monotonic()-start,flush=True)
    a,c=Fbox(Q(1,12));l,r=Fbox(Q(1));src,obs,coef=data(bs,k,k2,dt,(a-r,c-l),n)
    L=np.zeros((n,n));el=np.zeros_like(L);eh=el.copy();fl=np.zeros(n);fh=fl.copy()
    for i in range(n):
        fs=I(0)
        for j in range(i+1):
            K=intersect(box(vals[i,j,0]),box(vals[j,i,0]));Kt=intersect(box(vals[i,j,1]),box(vals[j,i,1]));Kx=box(vals[j,i,2]);v=-bs[j]/sqrt(1+bs[j]*bs[j]);ell=2*(Kx-v*Kt+1.5*K/bs[j]);E=ell*dt
            if j<i:
                vb=-b[j+1]/np.sqrt(1+b[j+1]**2);L[i,j]=float(2*(p[j,i,2]-vb*p[i,j,1]+1.5*p[i,j,0]/b[j+1])*dt);E=E-I(L[i,j])
            else:
                zmin=max(rat(Q(1,13)).l,(bs[j]-I(dt)/2).l);M=(k2+rat(Q(15,4))/(I(zmin)*I(zmin))).h;y=(I(M)*I(dt)*I(dt)/4).h
                if y<.5:
                    kk=(I(1)/(2*(1-I(y)))).h;der=(I(M)*I(dt)/(4*(1-I(y)))).h;local=(2*(I(der)*(1+absup(v))+1.5*I(kk)/bs[j])*dt).h;E=intersect(E,I(-local,local))
            el[i,j],eh[i,j]=E.l,E.h;term=-2*K*src[j]*dt;fs=fs+(hull(I(0),term) if i==j else term)
        fl[i],fh[i]=fs.l,fs.h
    A=np.eye(n)-L;G=solve_triangular(A,np.eye(n),lower=True);assert np.all(np.diag(G)==1) and not np.any(np.triu(G,1));err=np.zeros_like(G)
    for i in range(n):
        for j in range(i):err[i,j]=(I(G[i,j])-isum(I(L[i,j:i])*I(G[j:i,j]))).mag()
    rho=max(isum(I(row)).h for row in err);gn=max(isum(I(abs(row))).h for row in G);assert rho<1;corr=(I(gn)*I(rho)/(1-I(rho))).h
    C=I(D(G-np.eye(n)-corr),U(G-np.eye(n)+corr));C.l[np.triu_indices(n)]=0;C.h[np.triu_indices(n)]=0
    Delta=I(el,eh);P=U(abs(G-np.eye(n))+corr);P=np.tril(P,-1)+np.eye(n);old=np.zeros_like(L);H=np.zeros_like(L)
    for i in range(n):
        for j in range(i+1):
            old[i,j]=isum(I(P[i,j:i+1])*I(Delta.mag()[j:i+1,j])).h
            # Effective signed kernel: Delta_ij(T,s)+ sum C_il avg_t Delta_lj(t,s).
            # The diagonal avg over t>s occupies an unknown fraction [0,1].
            if j==i:H[i,j]=Delta[i,j].mag();continue
            av=I(Delta.l[j:i,j].copy(),Delta.h[j:i,j].copy());av.l[0]=min(0,av.l[0]);av.h[0]=max(0,av.h[0]);z=Delta[i,j]+isum(C[i,j:i]*av);H[i,j]=min(old[i,j],z.mag())
    f=(fl+fh)/2;x=solve_triangular(A,f,lower=True);rl=[];rh=[]
    for i in range(n):
        z=I(fl[i],fh[i])+isum(I(L[i,:i])*I(x[:i]))-I(x[i]);z=z+isum(Delta[i,:i]*I(x[:i]))+hull(I(0),Delta[i,i]*I(x[i]));rl.append(z.l);rh.append(z.h)
    rv=I(rl,rh);d=[];dr=[]
    for i in range(n):
        z=rv[i]+isum(C[i,:i]*rv[:i]);d.append(z.mag());dr.append(isum(I(P[i,:i+1])*I(rv.mag()[:i+1])).h)
    # Comparison uses same signed residual; direct full operator remains independent.
    olde=propagate(old,dr);new=propagate(H,d);direct=propagate((Delta+I(L)).mag(),rv.mag());best=[min(a,b,c) for a,b,c in zip(olde,new,direct)]
    out=[]
    for row in obs:
        q=I([z.l for z in row],[z.h for z in row]);signed=isum(q*I(x)*dt)
        with localcontext() as cc:
            cc.prec=40;cc.rounding=ROUND_CEILING
            def rad(e):return sum((Decimal.from_float(float(v))*ee for v,ee in zip((absup(q)*dt).h,e)),Decimal(0))
            # Goal-dual qhat=Rhat* q; preserve signed coarse feedback before abs.
            w=[]
            for j in range(n):w.append(q[j]+isum(C[j+1:,j]*q[j+1:]))
            W=I([z.l for z in w],[z.h for z in w]);cor=isum(W*rv*dt);goal=[]
            for j in range(n):goal.append((hull(I(0),W[j]*Delta[j,j])+isum(W[j+1:]*Delta[j+1:,j])).mag())
            goalrad=sum((Decimal.from_float(float(v))*ee for v,ee in zip((I(goal)*dt).h,best)),Decimal(0))
            out.append(dict(reconstruction=[float(signed.l),float(signed.h)],old_radius=str(rad(olde)),signed_radius=str(rad(new)),best_radius=str(rad(best)),goal_correction=[float(cor.l),float(cor.h)],goal_remainder=str(goalrad)))
    return dict(mode=mode,n=n,seconds=time.monotonic()-start,exact_checks=exact(),diagonal_max=float(np.max(np.diag(H))),old_row_max=float(max(isum(I(row)).h for row in old)),signed_row_max=float(max(isum(I(row)).h for row in H)),old_last=str(olde[-1]),signed_last=str(new[-1]),direct_last=str(direct[-1]),best_last=str(best[-1]),improved_blocks=int(np.sum(H<old)),finite_inverse_defect=float(rho),schur=schur(A,f,x),observer=out,scope='conditional whole-slab signed bounds; Schur diagnostic of finite matrix, not continuum coarsening or TT certificate')
if __name__=='__main__':print(json.dumps(run(int(sys.argv[1]),int(sys.argv[2])),indent=2),flush=True)
