"""XCV DC matrix matching and nonlinear periodic diagnostics, synthetic only.
J31 linear off-guard equations from XCIV donor 8dbdda4ab62ca5667764c2df90b2bb5a1c2a7beb.
"""
import json
import numpy as np
import sympy as S
from scipy.linalg import expm
from scipy.integrate import solve_ivp
from scipy.optimize import root
Q=S.Rational

def exact():
    M=S.Matrix([[2,Q(3,5)],[Q(3,5),Q(3,2)]]); N=S.Matrix([[Q(7,5),-1],[-1,Q(31,20)]])
    z=S.Matrix(S.symbols('i j u v b q r ih x',real=True));i,j,u,v,b,q,r,ih,x=z
    f=(M.inv()*S.Matrix([-Q(35,100)*i,u-v-Q(28,100)*j])).col_join(N.inv()*S.Matrix([-j+Q(35,100)*q+2*ih,j])).col_join(S.Matrix([-Q(18,1000)*b/Q(65,100),Q(11,10)*r-Q(2,10000)*q-Q(35,100)*u/2,-Q(11,10)*q-Q(2,10000)*r,(-x-Q(5,100)*ih-2*u)/Q(15,100),(ih-Q(52,100)*x)/Q(12,100)]))
    A=f.jacobian(z); K=S.zeros(2,9);K[0,5]=K[1,6]=1
    W=S.diag(M,N,Q(65,100),2,2,Q(15,100),Q(12,100)); loss=S.diag(Q(35,100),Q(28,100),0,0,Q(18,1000),Q(4,10000),Q(4,10000),Q(5,100),Q(52,100))
    assert A.T*W+W*A==-2*loss and W*K.T==2*K.T
    Z=-Q(15,1000)*K*A.inv()*K.T; Zs=(Z+Z.T)/2; Za=(Z-Z.T)/2
    assert Z==S.Matrix([[62400,343200000],[-343200000,9488775]])/25168126517
    # Avoid irrational coordinates by factoring the common rad=sqrt(.03).
    X=-A.inv()*K.T/2; row=X[-1,:]; U=Q(52,100)*Q(3,100)*row.T*row
    assert Zs==Q(3,100)*X.T*loss*X
    assert U.rank()==1 and (Zs-U).is_positive_definite
    opt=S.factor((U*Zs.inv()).trace()); direction=Zs.inv()*row.T
    assert U*direction==opt*Zs*direction
    C=S.Matrix([[1,-1],[0,1]]); H=Q(1,5)*S.eye(2)+Q(20,9)*C*C.T
    # Ideal transformer: circuit effort T E, Maxwell current T^T Jc.
    # Ideal skew current Jg=-T^T Za T E is instantaneous zero work.
    T=S.Matrix(2,2,S.symbols('t0:4',real=True)); E=S.Matrix(S.symbols('e:2',real=True)); Jg=-T.T*Za*T*E
    assert S.expand(E.dot(Jg))==0
    # Exact full-rank matched DC construction, not a broadband claim.
    T0=100*S.eye(2); Y=H+T0.T*Zs*T0
    assert Y.is_positive_definite
    # Current balance with incident power coordinate a=Y^(-1/2) Y E.
    assert H+T0.T*Z*T0-T0.T*Za*T0==Y
    # Pure transformer congruence preserves skew rank for nonsingular T.
    assert (T.T*Za*T)[0,1]==Za[0,1]*T.det()
    return A,K,Z,Zs,Za,U,H,opt,direction

A,K,Z,Zs,Za,U,H,opt,direction=exact()
An,Kn,Zsn,Zan,Hn=map(lambda x:np.array(x,float),(A,K,Zs,Za,H)); C=np.array([[1.,-1.],[0.,1.]])
print('opt',opt,float(opt),'direction',direction,'Zs',Zs, 'U',U,flush=True)

def model(beta,kind):
    d=np.array(direction,float).ravel();d/=np.linalg.norm(d)
    T=beta*(np.outer(d,[0.,1.]) if kind=='rank1_reciprocal' else np.eye(2))
    skew= -T.T@Zan@T if kind=='full_gyrator' else np.zeros((2,2))
    Y=Hn+T.T@Zsn@T
    ev,V=np.linalg.eigh(Y); R=(V*np.sqrt(ev))@V.T
    e=np.array([0.,1.]) if kind=='rank1_reciprocal' else d
    a=R@e; a/=np.linalg.norm(a)
    A=np.zeros((19,19)); B=np.zeros(19);B[:2]=R@a
    A[:2,:2]=-(.2*np.eye(2)+Y+skew)/2;A[:2,2:4]=C/2;A[:2,6:8]=-np.eye(2)/2;A[2:4,:2]=-C.T/1.5;A[2:4,8:10]=-np.eye(2)/1.5;A[4:6,6:8]=np.eye(2);A[6:8,:2]=1.5*np.eye(2);A[6:8,4:6]=-4*np.eye(2);A[6:8,6:8]=-2/3*np.eye(2);A[8:10,2:4]=10*np.eye(2);A[8:10,8:10]=-200/9*np.eye(2);A[10:,10:]=An;A[:2,10:]=-np.sqrt(.03)*T.T@Kn/2;A[10:,:2]=np.sqrt(.03)*Kn.T@T/2
    return A,B,R,a,T,skew

def spectrum(beta,kind,N=256):
    A,B,*_=model(beta,kind);n=np.arange(N+1);ak=.25*np.sinc(n/4)*np.exp(-2j*np.pi*n*.625)
    z=np.linalg.solve(1j*(2*np.pi*n/.4)[:,None,None]*np.eye(19)-A,(ak[:,None]*B)[...,None])[...,0]
    terms=.52*abs(z[:,-1])**2; terms[1:]*=2
    return dict(beta=beta,kind=kind,eta=float(4*sum(terms)),dc_eta=float(4*terms[0]),decay=float(-max(np.linalg.eigvals(A).real)))

def nonlinear(beta,kind):
    A,B,R,a,T,skew=model(beta,kind); aug=np.zeros((20,20));aug[:19,:19]=A;aug[:19,19]=B;E=expm(.1*aug);F=E[:19,:19];b=E[:19,19];guess=np.linalg.solve(np.eye(19)-np.linalg.matrix_power(F,4),F@b)
    def flow(z,ledger=False):
        states=[]; total=np.zeros(6);state=z.copy()
        for k in range(4):
            active=float(k==2)
            def f(t,y):
                x=y[:19];d=A@x+active*B;d[-1]/=1+1.5*x[-1]**2
                if not ledger:return d
                e=x[:2];v=x[6:8];eb=x[8:10];i,j,u,vv,bank,q,r,ih,cap=x[10:]; out=R@e-active*a
                return np.r_[d,active, out@out,.52*cap**2,.2*(e@e)+4/9*(v@v)+20/9*(eb@eb),.35*i*i+.28*j*j+.018*bank**2+.0004*(q*q+r*r)+.05*ih**2, e@(np.sqrt(.03)*T.T@np.array([q,r]))]
            sol=solve_ivp(f,(0,.1),np.r_[state,np.zeros(6)] if ledger else state,method='Radau',rtol=1e-9,atol=1e-11,dense_output=ledger)
            assert sol.success;state=sol.y[:19,-1]
            if ledger:total+=sol.y[19:,-1];states.append(sol.sol(np.linspace(0,.1,101))[:19,:])
        return (state,total,np.hstack(states)) if ledger else state
    res=root(lambda z:flow(z)-z,guess,tol=1e-9);z=res.x;end,tot,tr=flow(z,True);err=np.linalg.norm(end-z,np.inf); gap=max(np.max(tr[12]-tr[14]),np.max(tr[13]-tr[14]));bank=np.max(tr[14]);
    return dict(beta=beta,kind=kind,eta=float(tot[2]/tot[0]),ledger=tot.tolist(),return_error=float(err),ledger_residual=float(tot[0]-sum(tot[1:5])),sampled_diode_gap=float(gap),sampled_bank_max=float(bank),sampled_cap_max=float(np.max(abs(tr[-1]))),sampled_off_guard_ok=bool(gap<.1 and bank<.006),root_success=bool(res.success),nonlinear_periodic_certificate=False)

if __name__=='__main__':
    rows=[spectrum(float(b),k) for k in ('rank1_reciprocal','full_reciprocal','full_gyrator') for b in (10,30,100,300,1000)]
    cases=[nonlinear(b,k) for k,b in [('rank1_reciprocal',100),('rank1_reciprocal',300),('full_gyrator',100),('full_gyrator',300)]]
    out=dict(status='EXACT_DC_CONSTRUCTION_AND_NUMERICAL_OFF_BRANCH_DIAGNOSTICS',dc_native_useful_fraction=str(opt),dc_native_direction=[str(x) for x in direction],dc_source_quarter_useful_ceiling=str(opt/4),linear=rows,nonlinear=cases,physical_admission=False,original_J36=False)
    print(json.dumps(out,indent=2))
