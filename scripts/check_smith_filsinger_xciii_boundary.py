"""XCIII: finite oriented electric boundary port, not physical apparatus admission."""
import json
import sympy as S
import numpy as np
from scipy.linalg import solve_continuous_lyapunov, expm
from numpy.polynomial.legendre import leggauss
from smith_filsinger_lorentz_ade_sympy import generator, energy
q=S.Rational

def model(cap=None, rank=2, y0=q(1,10), y1=q(1000), g=q(1000)):
    A,B,M=generator(n=2,load_conductance=0); A=S.Matrix(A)
    Y=S.diag(y0,y1); root=S.diag(S.sqrt(y0),S.sqrt(y1))
    A[:2,:2]-=(Y+S.diag(0,g))/2; B=2*B*root
    # Btrace columns are signed boundary electric circulation traces.
    L=S.eye(2)[:,:rank]; R=q(9,20)*S.eye(rank)
    if cap is None:
        A[2:4,2:4]-=L*R*L.T/q(3,2)
    else:
        A=A.row_join(S.zeros(8,rank)).col_join(S.zeros(rank,8+rank))
        A[2:4,8:]=-L/q(3,2); A[8:,2:4]=L.T/cap
        A[8:,8:]=-R.inv()/cap; B=B.col_join(S.zeros(rank,2)); M=S.diag(M,cap*S.eye(rank))
    z=S.Matrix(S.symbols('z:'+str(A.rows),real=True)); a=S.Matrix(S.symbols('a:2',real=True))
    e=z[:2,:]; h=z[2:4,:]; v=z[6:8,:]; b=root*e-a
    eb=R*L.T*h if cap is None else z[8:,:]
    heat=(eb.T*R.inv()*eb)[0]
    loss=g*e[1]**2+q(1,5)*e.dot(e)+q(4,9)*v.dot(v)+heat
    assert S.expand((z.T*M*(A*z+B*a))[0]-a.dot(a)+b.dot(b)+loss)==0
    return A,B,M,root,R,L,g

def ldl_positive(A):
    L,D=A.LDLdecomposition(hermitian=False)
    assert L*D*L.T==A and all(v>0 for v in D.diagonal())
    return min(D.diagonal())

def rate(A,rate):
    # Floating candidate only; exact rational LDL validates strict inequality.
    n=A.rows; F=A+rate*S.eye(n)
    p=solve_continuous_lyapunov(np.array(F,dtype=float).T,-np.eye(n))
    P=S.Matrix(n,n,lambda i,j:q(round((p[i,j]+p[j,i])*5e9),10**10))
    d=ldl_positive(P); e=ldl_positive(-(F.T*P+P*F))
    return {'rate':str(rate),'P':[[str(v) for v in row] for row in P.tolist()], 'min_P_LDL_pivot':float(d),'min_dissipation_LDL_pivot':float(e)}

def run(cap=None,rank=2):
    A,B,M,root,R,L,g=model(cap,rank); A0=A
    A,B,M,root,R,L=map(lambda a:np.array(a,dtype=float),(A,B,M,root,R,L)); g=float(g); n=len(A)
    aug=np.zeros((n+2,n+2));aug[:n,:n]=A;aug[:n,n:]=B
    F=expm(.1*aug);T=F[:n,:n];D=F[:n,n:];mon=np.linalg.matrix_power(T,4)
    # Original external pulses 1/sqrt(2) each, one-bin delay and 45-degree mixer.
    ext=np.array([[0.,0.],[2**-.5,0.],[0.,2**-.5],[0.,0.]])
    mix=np.array([[1.,-1.],[1.,1.]])/np.sqrt(2)
    inner=np.array([mix@np.array([ext[(j-1)%4,0],ext[j,1]]) for j in range(4)])
    w=np.zeros(n)
    for a in inner:w=T@w+D@a
    z0=np.linalg.solve(np.eye(n)-mon,w)
    xs,ws=leggauss(24); edges=np.r_[0.,np.geomspace(1e-7,.1,20)]
    Q=[((hi-lo)*v/2,expm((lo+(u+1)*(hi-lo)/2)*aug)[:n,:]) for lo,hi in zip(edges[:-1],edges[1:]) for u,v in zip(xs,ws)]
    Ri=np.linalg.inv(R)
    def cycle(z):
        init=z.copy(); vals=np.zeros(6); reverse_energy=[]
        for a in inner:
            vals[0]+=.1*(a@a);rev=0.
            for weight,F in Q:
                x=F@np.r_[z,a];e=x[:2];h=x[2:4];v=x[6:8];b=root@e-a;eb=R@L.T@h if cap is None else x[8:]
                vals[1:]+=weight*np.array([b@b,g*e[1]**2,.2*(e@e),4/9*(v@v),eb@Ri@eb]); rev+=weight*(mix.T@b)[0]**2
            reverse_energy.append(rev);z=T@z+D@a
        change=(z@M@z-init@M@init)/2
        return z,vals,reverse_energy,change
    z,v,rev,ds=cycle(z0);assert abs(v[0]-sum(v[1:])-ds)<1e-9
    # Full cold-start: last bin has zero incident, but return delay still stores energy.
    # Previous reverse store zero for the first period; after N periods it is last-bin return energy.
    z=np.zeros(n); totals=np.zeros(6); last=0.; out=[]
    for k in range(1,101):
        z,vv,revv,dd=cycle(z);totals+=vv;last=revv[-1]
        if k in (1,10,100):
            stored=z@M@z/2;external_ref=totals[1]-last
            resid=totals[0]-external_ref-sum(totals[2:])-stored-last
            assert abs(resid)<1e-8
            out.append(dict(cycles=k,eta=totals[2]/totals[0],delay_return_storage=last,receiver_storage=stored,external_reflected=external_ref,residual=resid))
    # Restored return store has same initial/final energy, so period reflection unchanged.
    return dict(cap=str(cap),rank=rank,eta=v[2]/v[0],ledger=v.tolist(),period_residual=v[0]-sum(v[1:])-ds,decay=-max(np.linalg.eigvals(A).real),rate_certificate=rate(A0,q(1,5)) if rank==2 else None,cold=out)

if __name__=='__main__':
    # Rank-two boundary required for exact isotropic dI; rank-one cannot equal it.
    assert (S.eye(2)[:,:1]*q(9,20)*S.eye(2)[:,:1].T).rank()==1
    rows=[run(),run(q(1,100)),run(q(1,10)),run(q(1,100),1)]
    print(json.dumps({'status':'PASS_FINITE_BOUNDARY_CONSTRUCTION','physical_trace_realization':False,'ledger_order':['incident','reflected','terminal','ohmic','relaxation','boundary_resistor'],'rows':rows},indent=2))
