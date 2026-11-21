"""Finite periodic Maxwell/material scattering with temporally modulated a=1/chi.
Synthetic 3x3 and 3x3x3 open-grid reference; no measured optical or Earth data.
"""
import numpy as np
import sympy as sp
from itertools import product
from scipy.sparse import csr_matrix,bmat
from scipy.sparse.linalg import lsmr

EPS,MU,ETA,H,G,LOAD,A=.85,.9,.35,.11,.3,.18,4.

def incidence(dim):
    vs=list(product(range(3),repeat=dim)); ix={v:i for i,v in enumerate(vs)}
    edges=[(p,j) for j in range(dim) for p in product(*(range(2 if i==j else 3) for i in range(dim)))]
    B=np.zeros((len(vs),len(edges)))
    for c,(p,j) in enumerate(edges):
        q=list(p);q[j]+=1; B[ix[p],c]=-1;B[ix[tuple(q)],c]=1
    return B

def exact():
    p,q,a,b,be=sp.symbols('p q a b be',real=True)
    U=lambda x,c:c*x*x/2+be*x**4/4
    discrete=(a+b)*(p+q)/4+be*(p+q)*(p*p+q*q)/4
    modulation=(b-a)*(p*p+q*q)/4
    assert sp.expand(U(q,b)-U(p,a)-(q-p)*discrete-modulation)==0
    g,v,e=sp.symbols('g v e',real=True)
    assert sp.expand(g*(v-e)*e-g*v*e+g*e*e)==0
    return 2

def solve(dim,beta,mod_amp,phase,period=8,drive_amp=.12,material_profile=None,return_history=False):
    B=incidence(dim); n,m=B.shape; size=2*n+m
    src=np.zeros(n);src[0]=1.;rec=np.zeros(n);rec[-1]=1.
    ss=np.outer(src,src);rr=np.outer(rec,rec)
    k=np.arange(period); theta=2*np.pi*k/period
    volt=.3+drive_amp*np.sin(theta)
    a=A+mod_amp*np.sin(theta+phase) if material_profile is None else np.asarray(material_profile,dtype=float)
    assert a.shape==(period,) and np.all(a>0)
    e=G*.3/(G+LOAD); p=e/A
    rhs=LOAD*e*rec-G*(.3-e)*src
    h=np.linalg.lstsq(B,rhs,rcond=None)[0]
    nodes=np.tile(np.r_[np.full(n,e),h,np.full(n,p)],(period,1))
    I=np.eye(n); Im=np.eye(m)
    def pair(x,y,j,jac=False):
        E0,H0,P0=np.split(x,[n,n+m]);E1,H1,P1=np.split(y,[n,n+m]);
        Em=(E0+E1)/2;Hm=(H0+H1)/2;dp=P1-P0
        a0=a[j];a1=a[(j+1)%period]
        coeff=(a0+a1)/4
        dg=coeff*(P0+P1)+beta*(P0+P1)*(P0*P0+P1*P1)/4
        r=np.r_[EPS*(E1-E0)+dp-H*(B@Hm+G*(volt[j]-Em[0])*src-LOAD*Em[-1]*rec),
                MU*(H1-H0)+H*B.T@Em,
                ETA*dp/H+dg-Em]
        if not jac:return r
        corner=H/2*(G*ss+LOAD*rr)
        d0=coeff+beta/4*(P0*P0+P1*P1+2*P0*(P0+P1))
        d1=coeff+beta/4*(P0*P0+P1*P1+2*P1*(P0+P1))
        zeros=np.zeros((n,m));zt=np.zeros((m,n))
        L=np.block([[-EPS*I+corner,-H*B/2,-I],
                    [H*B.T/2,-MU*Im,zt],
                    [-I/2,zeros,np.diag(-ETA/H+d0)]])
        R=np.block([[EPS*I+corner,-H*B/2,I],
                    [H*B.T/2,MU*Im,zt],
                    [-I/2,zeros,np.diag(ETA/H+d1)]])
        return r,L,R
    def residual(v, jac=False):
        v=v.reshape((period,size));rs=[]
        blocks=[[None]*period for _ in range(period)] if jac else None
        for j in range(period):
            nxt=(j+1)%period
            if jac:
                r,L,R=pair(v[j],v[nxt],j,True)
                blocks[j][j]=csr_matrix(L);blocks[j][nxt]=csr_matrix(R)
            else:r=pair(v[j],v[nxt],j)
            rs.append(r)
        return (np.concatenate(rs),bmat(blocks,format='csr')) if jac else np.concatenate(rs)
    for it in range(22):
        res,J=residual(nodes,True); norm=np.max(np.abs(res))
        if norm<1e-11:break
        delta=lsmr(J,-res,atol=1e-13,btol=1e-13,maxiter=3500)[0].reshape(nodes.shape)
        fraction=1.
        while fraction>1/128 and np.max(np.abs(residual(nodes+fraction*delta)))>=norm:
            fraction/=2
        nodes+=fraction*delta
    defect=np.max(np.abs(residual(nodes)))
    assert defect<1e-9,(dim,beta,mod_amp,phase,defect)
    total=np.zeros(6)
    max_ledger=0.
    for j in range(period):
        E0,H0,P0=np.split(nodes[j],[n,n+m]);E1,H1,P1=np.split(nodes[(j+1)%period],[n,n+m]);Em=(E0+E1)/2
        ext=H*G*volt[j]*Em[0]; src_loss=H*G*Em[0]**2
        load=H*LOAD*Em[-1]**2;relax=ETA*np.dot(P1-P0,P1-P0)/H
        mod=(a[(j+1)%period]-a[j])*np.dot(P0,P0)/4+(a[(j+1)%period]-a[j])*np.dot(P1,P1)/4
        def energy(E,HH,P,coeff):
            return (EPS*np.dot(E,E)+MU*np.dot(HH,HH)+coeff*np.dot(P,P))/2+beta*np.sum(P**4)/4
        du=energy(E1,H1,P1,a[(j+1)%period])-energy(E0,H0,P0,a[j])
        err=du-ext+src_loss+load+relax-mod
        max_ledger=max(max_ledger,abs(err));assert abs(err)<1e-9,(dim,j,err)
        total+=np.array([ext,src_loss,load,relax,mod,du])
    assert abs(total[-1])<1e-9
    assert abs(total[0]+total[4]-sum(total[1:4]))<1e-9
    mid=(nodes+np.roll(nodes,-1,axis=0))/2
    Psignal=mid[:,n+m]
    Enear=mid[:,1]
    Vhat=np.fft.fft(volt)[1]/period
    Phat=np.fft.fft(Psignal)/period
    Ehat=np.fft.fft(Enear)[1]/period
    result=dict(near=Ehat/Vhat,p1=Phat[1],p2=Phat[2],ledger=max_ledger,defect=defect,
                external=total[0],source_loss=total[1],load=total[2],relax=total[3],modulation=total[4])
    if return_history:
        result["states"]=nodes.copy()
        result["material_profile"]=a.copy()
        result["midpoints"]=mid.copy()
        result["source_profile"]=volt.copy()
    return result

def main():
    checks=exact()
    for dim in (2,3):
        for beta in (0.,.45):
            baseline=solve(dim,beta,0.,0.)
            for phase in (0.,np.pi/2):
                r=solve(dim,beta,.3,phase)
                assert r['defect']<1e-9 and r['ledger']<1e-9;checks+=1
                assert abs(r['modulation'])>1e-10;checks+=1
                assert abs(r['near']-baseline['near'])>1e-7;checks+=1
                assert abs(r['p2']-baseline['p2'])>1e-9;checks+=1
                print('case',dim,beta,'phase',phase,'near',r['near'],'p2',abs(r['p2']),'mod',r['modulation'],'load',r['load'])
            r0=solve(dim,beta,.3,0.)
            r90=solve(dim,beta,.3,np.pi/2)
            assert abs(r0['near']-r90['near'])>1e-8;checks+=1
            assert abs(baseline['modulation'])<1e-12;checks+=1
    print(f'{checks}/{checks} PASS; SymPy {sp.__version__}')

if __name__=='__main__':main()
