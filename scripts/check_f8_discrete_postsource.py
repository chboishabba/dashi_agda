"""Original mode3 SBP/SAT postsource parity elliptic algebra and obstruction.
No source-on trajectory, kernel proof or numerical convergence claim.
"""
import json
import sympy as S
import numpy as np


def sbp(n,h):
    D=np.zeros((n,n));D[0,:2]=[-1,1];D[-1,-2:]=[-1,1]
    for j in range(1,n-1):D[j,j-1],D[j,j+1]=-.5,.5
    H=np.full(n,h);H[[0,-1]]=h/2
    return D/h,H


def exact():
    count=0
    def eq(x,y=0):
        nonlocal count
        assert S.simplify(x-y)==0,(x,y);count+=1
    v,vt,h,G,W0,W1,WN,Wm,N0,NN=S.symbols('v vt h G W0 W1 WN Wm N0 NN',real=True)
    a,c=1+v,1-v;s=a*c
    F=v*W0+s*N0;P=WN+c*NN
    satM=4*(F-G)/h;satP=-2*a*P/h
    nt0=(W1-W0)/h-satM/2;ntN=(WN-Wm)/h+satP/2
    eq(s*N0,(W1-W0)/2-h*nt0/2+G-v*W0)
    eq(s*NN,WN-Wm-h*ntN-a*WN)
    W,N,DW,DN,U,K,z,SP,SM=S.symbols('W N DW DN U K z SP SM',real=True)
    Pd=a*(DW+c*DN)-K*U-3*N/z+SP
    Md=-c*(DW-a*DN)-K*U-3*N/z+SM
    eq((Pd-Md)/2,DW+(SP-SM)/2)
    eq((a*Pd+c*Md)/2+vt*N,2*v*DW+s*DN-K*U+(vt-3/z)*N+(a*SP+c*SM)/2)
    for n in (5,6,7,8):
        D=S.zeros(n);D[0,0]=-1;D[0,1]=1;D[-1,-2]=-1;D[-1,-1]=1
        for j in range(1,n-1):D[j,j-1]=-S.Rational(1,2);D[j,j+1]=S.Rational(1,2)
        D/=h;H=S.diag(h/2,*([h]*(n-2)),h/2)
        U=S.Matrix(S.symbols('u:'+str(n)));N=D*U;N[0]=N0;N[-1]=NN
        E=S.diag(-1,*([0]*(n-2)),1)
        assert H*D+D.T*H==E;count+=1
        rhs=-h*sum(N[j]**2 for j in range(1,n-1))-(U[0]+U[1])*N0/2+(U[-1]+U[-2])*NN/2
        eq((U.T*H*D*N)[0],rhs)
        # General mixed time-jet version, interior D U_i=N_i independent.
        V=S.Matrix(S.symbols('w:'+str(n)));M=D*V;M[0]=S.Symbol('m0');M[-1]=S.Symbol('mn')
        rhs=-h*sum(N[j]*M[j] for j in range(1,n-1))-(U[0]+U[1])*M[0]/2+(U[-1]+U[-2])*M[-1]/2
        eq((U.T*H*D*M)[0],rhs)
    return count


def obstruction():
    # Original clock t=4/3, instant transformed W,N generator, arbitrary
    # admissible interior constraint state. Freeze only for graph test.
    v=-.6;s=1-v*v;a,c=1+v,1-v;b=.75;vt=192/625
    out=[]
    for n in (81,129,257):
        h=2.016/(n-1);D,H=sbp(n,h);I=np.eye(n);E=I.copy();E[[0,-1],[0,-1]]=0
        C=s*D+np.diag(vt-3/(b+h*np.arange(n)))
        C[0,0]+=2*c*s/h;C[-1,-1]-=a*s/h
        q=np.zeros(n);q[0]=1
        for R in (10.,100.,1000.,10000.):
            U=np.linalg.solve(R*R*I-C@E@D,C@q);N=E@D@U+q
            W=np.zeros(n);Wt=C@N-R*R*U;Nt=np.zeros(n);Nt[0]=-2*s/h*N[0];Nt[-1]=-s/h*N[-1]
            energy=lambda u,w,n0:float(np.sqrt(np.sum(H*(R*R*u*u+w*w+s*n0*n0))))
            e=energy(U,W,N);e1=energy(W,Wt,Nt)
            assert np.max(abs(Wt))<1e-10 and np.max(abs(N[1:-1]-(D@U)[1:-1]))<1e-12
            out.append(dict(n=n,h=h,R=R,rate=e1/e,R_times_state_over_rate=R*e/e1,rho_times_state_over_rate=min(R,1/h)*e/e1,Wt_max=float(max(abs(Wt)))))
    assert out[3]['R_times_state_over_rate']>100
    return out


if __name__=='__main__':print(json.dumps(dict(exact_checks=exact(),instant_graph_negative_controls=obstruction(),scope='original mode3 exact restricted SBP and endpoint identities, frozen admissible graph negative control; not source-on evolution or kernel'),indent=2))
