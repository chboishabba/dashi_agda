"""XCIV loaded small-signal feedback admittance. Not a nonlinear periodic proof."""
import json
import numpy as np
import sympy as S
from scipy.linalg import expm
Q=S.Rational

def circuit():
    # Zero-equilibrium Jacobian of original capacitive return with both diodes
    # and spark OFF. Radiation is replaced by signed feedback port.
    i,j,u,v,b,q,r,ih,x=S.symbols('i j u v b q r ih x',real=True)
    z=S.Matrix([i,j,u,v,b,q,r,ih,x]); M=S.Matrix([[2,Q(3,5)],[Q(3,5),Q(3,2)]]); N=S.Matrix([[Q(7,5),-1],[-1,Q(31,20)]])
    f=(M.inv()*S.Matrix([-Q(35,100)*i,u-v-Q(28,100)*j])).col_join(N.inv()*S.Matrix([-j+Q(35,100)*q+2*ih,j])).col_join(S.Matrix([-Q(18,1000)*b/Q(65,100),Q(11,10)*r-Q(2,10000)*q-Q(35,100)*u/2,-Q(11,10)*q-Q(2,10000)*r,(-x-Q(5,100)*ih-2*u)/Q(15,100),(ih-Q(52,100)*x)/Q(12,100)]))
    A=f.jacobian(z); K=S.zeros(2,9);K[0,5]=K[1,6]=1
    W=S.diag(M,N,Q(65,100),2,2,Q(15,100),Q(12,100))
    diss=S.diag(Q(35,100),Q(28,100),0,0,Q(18,1000),Q(4,10000),Q(4,10000),Q(5,100),Q(52,100))
    assert A.T*W+W*A==-2*diss
    assert W*K.T==2*K.T
    # DC admittance for feedback port J=beta rad K z; zdot=A z+beta rad K^T E/2.
    Z=-Q(15,1000)*K*A.inv()*K.T
    assert Z+Z.T==Q(15,1000)*K*A.T.inv()*diss*A.inv()*K.T
    # Frequency-independent passivity identity from resolvent and exact dissipation.
    # Re Z(jw)=B^*R^*D R B >=0, using W A+A^T W=-2D.
    return A,K,Z

A,K,Z=circuit(); An=np.array(A,float); Kn=np.array(K,float); C=np.array([[1.,-1.],[0.,1.]])

def matrix(beta,y1):
    Y=np.array([.1,y1]);root=np.sqrt(Y);a=np.zeros((19,19));b=np.zeros((19,2));b[:2]=np.diag(root)
    a[:2,:2]=-np.diag(.2+Y)/2;a[:2,2:4]=C/2;a[:2,6:8]=-np.eye(2)/2;a[2:4,:2]=-C.T/1.5;a[2:4,8:10]=-np.eye(2)/1.5;a[4:6,6:8]=np.eye(2);a[6:8,:2]=1.5*np.eye(2);a[6:8,4:6]=-4*np.eye(2);a[6:8,6:8]=-2/3*np.eye(2);a[8:10,2:4]=10*np.eye(2);a[8:10,8:10]=-200/9*np.eye(2)
    a[10:,10:]=An;a[:2,10:]=-beta*np.sqrt(.03)*Kn/2;a[10:,:2]=beta*np.sqrt(.03)*Kn.T/2
    return a,b

def spectrum(beta,y1,N=128):
    a,b=matrix(beta,y1); n=np.arange(N+1);w=2*np.pi*n/.4
    # pulse [0.2,0.3), Fourier coefficients with phase retained.
    ak=.25*np.sinc(n/4)*np.exp(-2j*np.pi*n*.625)
    rhs=np.tile(b[:,1],(N+1,1))*ak[:,None]
    states=np.linalg.solve(1j*w[:,None,None]*np.eye(19)-a,rhs[...,None])[...,0]
    terms=.52*np.abs(states[:,-1])**2;terms[1:]*=2
    # total time-average incident power 1/4. Truncated Fourier diagnostic only.
    eta=4*sum(terms);return eta,4*terms[0],states

def candidate(beta,y1):
    eta,dc,_=spectrum(beta,y1,256);a,b=matrix(beta,y1); aug=np.zeros((20,20));aug[:19,:19]=a;aug[:19,19]=b[:,1];ex=expm(.1*aug);T=ex[:19,:19];v=ex[:19,19];mon=np.linalg.matrix_power(T,4);z0=np.linalg.solve(np.eye(19)-mon,T@v)
    z=z0.copy(); mx=-np.inf; xv=0.
    for k in range(4):
        for t in np.linspace(0,.1,33):
            x=(expm(t*aug)@np.r_[z,float(k==2)])[:19];mx=max(mx,x[12]-x[14],x[13]-x[14]);xv=max(xv,abs(x[18]))
        z=T@z+(v if k==2 else 0)
    return dict(beta=float(beta),Y1=float(y1),eta=float(eta),dc_eta=float(dc),spectral_radius=float(max(abs(np.linalg.eigvals(mon)))),linear_sample_max_diode_gap=float(mx),linear_sample_max_abs_HF_cap=float(xv),linear_state_return_error=float(np.linalg.norm(z-z0)),nonlinear_periodic_certificate=False)

if __name__=='__main__':
    rows=[]
    for beta in np.geomspace(.3,300,31):
        for y1 in np.geomspace(.03,3000,31):
            eta,dc,_=spectrum(beta,y1);rows.append((float(eta),float(beta),float(y1)))
    rows.sort(reverse=True);best=rows[0];out={'status':'PASS_EXACT_SMALL_SIGNAL_PASSIVITY_NUMERICAL_SPECTRAL_SCAN','dc_admittance_per_beta_squared':[[str(v) for v in row] for row in Z.tolist()],'grid_cases':len(rows),'harmonic_truncation_scan':128,'harmonic_truncation_recheck':256,'baseline':candidate(10,1),'top':candidate(best[1],best[2]),'grid':rows,'nonlinear_guard_admission':False,'physical_admission':False};print(json.dumps(out,indent=2))
