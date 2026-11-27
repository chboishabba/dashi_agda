"""Full frozen F8 GN tensor collar + material/Israel/gauge rows.
Finite outer Dirichlet and frozen time; numerical diagnostics, not continuum acceptance.
"""
import numpy as np
import sympy as S
from scipy.sparse import diags, block_diag, kron, eye
from scipy.sparse.linalg import splu
from check_f8_gn_tensor_transfer import coefficients, ids

E=np.diag([-1.,1.,1.,1.]); I=np.eye(4)

def pack(p):return np.array([p[i,j] for i,j in ids],complex)
def unpack(v):
    p=np.zeros((5,5),complex)
    for (i,j),a in zip(ids,v):p[i,j]=p[j,i]=a
    return p

def material(t,s,k,p,r=1/16):
    """Freeze full FRW material EL after differentiating coefficients.
    Physical v=t delta X, u=delta phi; k is physical wall covector.
    """
    b=1/t; B=np.sqrt(1+b*b); w=4*r*b**4/3; K=b*b/(3*B)-w
    Kt=-b**3*(2+b*b)/(3*B**3)+4*b*w
    rhot=-b**3/B; pt=-rhot-b**3*(2+b*b)/(3*B**3)
    l=p[0,0]; m=p[1:,0]; J=p[1:,1:]; tr=np.trace(J); q=k@k
    u=(-(s/2)*(l+tr)+1j*k@m-(3*b+Kt/(2*K))*l)/(s*s+(3*b+Kt/K)*s+q+3*b*b)
    v=np.linalg.solve((s*s-b*s+b*b)*np.eye(3)+np.outer(k,k)/3,s*m-1j*k*(tr/6+l/2))
    # Full material-coordinate pullback, including time-dependent background.
    D=1j*k@v-tr/2; L=s*u+l/2; vel=(s-b)*v
    dr=w*D+K*L+(rhot+3*b*w)*u
    dp=w*D/3+K*L+(pt+b*w)*u
    T=np.diag([-dr,dp,dp,dp]).astype(complex)
    T[0,1:]=w*(m-vel)-K*1j*k*u
    T[1:,0]=w*vel+K*(m+1j*k*u)
    return T,u,v

def rows(t,s,k,p,dn):
    """4 mixed Dirichlet, 10 Israel and 1 normal gauge, in packed order.
    dn is derivative in the normal-parallel orthonormal frame.
    """
    b=1/t; B=np.sqrt(1+b*b); K0=np.diag([-1/B,-B,-B,-B]); tau=np.trace(K0)
    h=p[:4,:4]; z=p[4,4]; w=p[:4,4]; dh=dn[:4,:4]
    T,_,_=material(t,s,k,h); K1=-3*T+np.trace(T)*I
    # Tangential FRW covector derivative of normal-mixed boundary value.
    D=np.outer(np.r_[s,1j*k],w)
    for i in range(1,4): D[i,i]-=b*w[0];D[i,0]-=b*w[i]
    R=dh-2*E@K1-h@K0+K0@h-D-D.T-z*E@K0
    C=dn[4,4]-np.trace(E@dh)+2*tau*z-2*np.trace(K0@E@h)+2*np.trace(E@D)
    out=np.zeros((5,5),complex);out[:4,:4]=R;out[:4,4]=out[4,:4]=w;out[4,4]=C
    assert np.max(abs(R-R.T))<1e-8*max(1,np.max(abs(R)))
    return pack(out)

def operator():
    t,n=S.symbols('t n',positive=True); A,N,Bt,Bx,V=coefficients(t,n)
    return S.lambdify((t,n),(A,N,N.diff(n),Bt,*Bx,V),'numpy',cse=True)

def transfer(fun,t,s,k,cells):
    """All 15 unit wall traces, zero outer trace at n=1/8.
    Centered second-order FD in proper n for the optical U equation.
    """
    d=1/(8*cells); n=np.arange(1,cells)*d; q=k@k; w=s*s+q
    blocks=[]; lo=[]; hi=[]
    for x in n:
        A,N,Nn,Bt,B1,B2,B3,V=fun(t,x)
        Q=(w+q*((N/A)**2-1))*np.eye(15)-s*Bt-1j*(k[0]*B1+k[1]*B2+k[2]*B3)-V
        blocks.append(-2*np.eye(15)/d**2-Q/N**2)
        lo.append(1/d**2-Nn/(2*d*N));hi.append(1/d**2+Nn/(2*d*N))
    size=cells-1
    M=block_diag(blocks,format='csc')+kron(diags([lo[1:],hi[:-1]],[-1,1],shape=(size,size)),eye(15),format='csc')
    rhs=np.zeros((15*size,15),complex);rhs[:15]=-lo[0]*np.eye(15)
    U=splu(M).solve(rhs)
    dtn=(3*np.eye(15)-4*U[:15]+U[15:30])/(2*d)
    # p=a^-3/2 U; normalize wall trace and undo normal conjugation.
    return -dtn+1.5*np.sqrt(1+t**-2)*np.eye(15)

def boundary(t,s,k,D):
    return np.column_stack([rows(t,s,k,unpack(e),unpack(D@e)) for e in np.eye(15)])

def exact():
    t=S.symbols('t',positive=True); b=1/t; B=S.sqrt(1+b*b); r=S.symbols('r',positive=True)
    w=4*r*b**4/3; K=b*b/(3*B)-w; rho=B-1;p=-rho+b*b/(3*B); V=(rho-p)/2-r*b**4/3
    assert S.simplify(K.diff(t)/2+3*b*K+V.diff(t))==0
    assert S.simplify(-3*b*K.diff(t)-K.diff(t,2)/2-V.diff(t,2)+3*b*b*K)==0
    assert S.diff(t**4*w,t)==0
    assert S.simplify(rho.diff(t)+3*b*(K+w))==0
    # Arbitrary symmetric h, normal frame vs coordinate jets.
    g=S.diag(-1,1,1,1); L=S.diag(-1/B,-B,-B,-B);tau=S.trace(L)
    h=S.Matrix(4,4,lambda i,j:S.Symbol('h%d%d'%(min(i,j),max(i,j))))
    dh=S.Matrix(4,4,lambda i,j:S.Symbol('d%d%d'%(min(i,j),max(i,j))))
    z,dz=S.symbols('z dz');coord=dh+L*h+h*L
    K1=g*coord/2-g*h*L-z*L/2
    assert (2*g*K1+h*L-L*h+z*g*L-dh).applyfunc(S.expand)==S.zeros(4)
    assert S.expand((dz-S.trace(g*coord))/2+tau*z-((dz-S.trace(g*dh))/2+tau*z-S.trace(L*g*h)))==0
    # Explicit conservative high-frequency sector budgets; see roadmap for inequalities.
    from fractions import Fraction as Q
    a=Q(1,1000); Bmax=2; x=10**18; gamma=10**18
    assert Q(1,32)**2<a
    assert Q(10000,a*x)<Q(1,2) and Q(31,a*x)<Q(1,2)
    assert Q(16000000*32,x)<Q(1,10)
    assert Q(32*10**11)*(Q(1,x)+Q(45*Bmax,gamma))<Q(1,10)
    return 10

def run():
    print('exact frame/FRW checks',exact(),flush=True); fun=operator(); worst=0.; errors=[]
    for t in (1.,3.,12.):
        for s,k in ((40+0j,np.zeros(3)),(40+100j,np.array([100.,0,0])),(40+100j,np.array([np.sqrt(3)*100,0,0]))):
            mats=[]
            for n in (128,256,512):
                D=transfer(fun,t,s,k,n); M=boundary(t,s,k,D)
                # All 15 residual rows including nonzero normal-mixed forcing.
                f=np.arange(1,16)*(1+.2j); x=np.linalg.solve(M,f)
                err=np.linalg.norm(M@x-f,np.inf)/np.linalg.norm(f,np.inf); worst=max(worst,err)
                assert err<1e-10
                mats.append(D)
            e1=np.linalg.norm(mats[1]-mats[0],np.inf); e2=np.linalg.norm(mats[2]-mats[1],np.inf)
            assert e2<.6*e1
            errors.append(e2/e1);print(t,s,k[0],'refinement ratio',e2/e1,flush=True)
    print('27 full boundary solves PASS; max residual',worst,'max refinement ratio',max(errors))

if __name__=='__main__':run()
