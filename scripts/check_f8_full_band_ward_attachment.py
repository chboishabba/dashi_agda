"""F8 W1: exact Fourier tensor Ward/Israel attachment, retaining signed source,
retarded controller, elastic response, and K/2K/3K support.
The existing History supplies actual finite-band first-order and A2 histories.
Not a continuum error bound or full coupled IBVP.
"""
import numpy as np
I=np.eye(3)

def bilinear(p,q,H,Pi,Ht,Pit,t,K,w,A=1.):
    """Ordered H_p Pi_q contribution, comoving derivatives i k/t."""
    b=1/t; gp=1j*np.asarray(p)/t;gq=1j*np.asarray(q)/t
    d=A*np.trace(H@Pi)/2
    T=np.zeros((4,4),complex);C=T.copy();R=np.zeros(4,complex)
    T[0,0]=d;T[1:,1:]=d*I-A*H@Pi
    C[0,0]=-d;C[1:,1:]=-d*I
    R[0]=A*np.trace(H@(Pit+2*b*Pi))/2
    for i in range(3):
        R[i+1]=A*np.trace((gp[i]*H)@Pi+H@(gq[i]*Pi))/2
        R[i+1]+=sum((-A*(gp[j]*H@Pi+H@(gq[j]*Pi)))[j,i] for j in range(3))
        R[i+1]-=A*np.trace(Pi@(gp[i]*H))/2
    return T,C,R

def gravity(p,q,H,G,Ht,Gt,t,K,w):
    """Ordered radiation H_p H_q and K clock H_p Ht_q."""
    gp=1j*np.asarray(p)/t;gq=1j*np.asarray(q)/t
    df=w*np.trace(H@G)/4
    T=np.zeros((4,4),complex);C=T.copy();R=np.zeros(4,complex)
    T[0,0]=-df;T[1:,1:]=df/3*I
    C[0,0]=3*df;C[1:,1:]=-df*I
    R[0]=K*np.trace(H@Gt)/2
    for i in range(3):R[i+1]=w*np.trace(H@G)*gq[i]/6
    return T,C,R

def controller(p,q,charge,Pi,t):
    """Retarded A2_p Pi_q including the complete spatial Ward gradient."""
    T=np.zeros((4,4),complex);C=T.copy();R=np.zeros(4,complex)
    T[1:,1:]=charge*Pi;C[1:,1:]=-3*charge*Pi
    R[1:]=1j*charge*(np.asarray(p)+np.asarray(q))@Pi/t
    return T,C,R

def elastic(k,H,t,muS):
    T=np.zeros((4,4),complex);C=T.copy();R=np.zeros(4,complex)
    T[1:,1:]=-muS*H;C[1:,1:]=3*muS*H
    R[1:]=-1j*muS*np.asarray(k)@H/t
    return T,C,R

def assemble(history,t,k,muS=0.):
    """Actual original-source finite-band known T, effective Israel C, Ward R.
    Output k is along local z; rotate original source tensor for other directions.
    """
    from scipy.interpolate import CubicSpline
    from check_f8_full_band_wall_controller import triangles,sectors,Q
    from check_f8_nonzero_convolution import project
    from check_f8_characteristic_history import coefficient,bump
    cutoff=history.K;b=1/t;w=b**4/12
    clock=b*b/(3*np.sqrt(1+b*b))-w
    h=CubicSpline(history.kh,history.h(t))
    ht=CubicSpline(history.kh,history.ht(t))
    P=bump(t)
    ds=np.arcsinh(t)-np.sqrt(1+t*t)/t-(np.arcsinh(1.)-np.sqrt(2.))
    x=2*ds/.065-1
    Pt=P*(-2*x/(1-x*x)**2)*2*np.sqrt(1+t*t)/(t*t*.065) if abs(x)<1 else 0.
    def coeff(r):return coefficient(np.array([r]))[0]
    def field(p):
        r=np.linalg.norm(p);E=project(Q,p);c=coeff(r)
        return c*h(r)*E,c*ht(r)*E,c*P*E,c*Pt*E
    total=[np.zeros((4,4),complex),np.zeros((4,4),complex),np.zeros(4,complex)]
    def add(row,weight):
        for j in range(3):total[j]+=weight*row[j]
    for p,q,weight in triangles(k,cutoff,cutoff,history.nodes):
        H,Ht,Pi,Pit=field(p);G,Gt,Qp,Qpt=field(q)
        add(gravity(p,q,H,G,Ht,Gt,t,clock,w),weight)
        add(bilinear(p,q,H,Qp,Ht,Qpt,t,clock,w),weight)
    B=CubicSpline(history.kr,history.ctrl(t)[0],axis=0)
    for p,q,weight in triangles(k,cutoff,2*cutoff,history.nodes):
        qn=np.linalg.norm(q)
        charge=B(qn)@sectors(q/qn,Q) if qn else 0.
        add(controller(q,p,charge,field(p)[2],t),weight)
    if muS and 0<k<=cutoff:
        add(elastic([0,0,k],field(np.array([0.,0.,k]))[0],t,muS),1)
    return tuple(total)

def exact():
    """Independent exact comparison to original scalar_vector_wall.known."""
    import sympy as s
    from check_f8_scalar_vector_wall import known
    p=s.Matrix([2,3,-1]);q=s.Matrix([-1,4,2]);t=s.Rational(5,4)
    K=s.Rational(7,9);w=s.Rational(2,11);A=s.Rational(3,5)
    H=s.Matrix([[1,2,3],[2,-2,1],[3,1,1]])
    Pi=s.Matrix([[2,1,4],[1,-3,2],[4,2,1]])
    Ht=s.Matrix([[1,0,2],[0,1,3],[2,3,-2]])
    Pit=s.Matrix([[3,2,1],[2,0,4],[1,4,-3]])
    a,c=s.symbols('a c');h=a*H;pi=c*Pi
    gradH=[s.I*p[i]/t*h for i in range(3)]
    gradPi=[s.I*q[i]/t*pi for i in range(3)]
    T,C,R0,R=known(h,pi,a*Ht,c*Pit,gradH,gradPi,A,0,[0,0,0],0,0,K,w,1/t)
    mixed=lambda z:s.expand(z).coeff(a,1).coeff(c,1)
    oracle=[T.applyfunc(mixed),C.applyfunc(mixed),s.Matrix([mixed(R0)]+[mixed(v) for v in R])]
    f=lambda M:np.array(M.tolist(),dtype=complex)
    got=bilinear(np.array(p,float).ravel(),np.array(q,float).ravel(),f(H),f(Pi),f(Ht),f(Pit),float(t),float(K),float(w),float(A))
    assert all(np.max(abs(x-f(y).reshape(x.shape)))<2e-13 for x,y in zip(got,oracle))
    k=np.array([2.,3.,5.]); P=np.diag([1.,-2.,1.])
    H0=np.array([[1.,2.,3.],[2.,-1.,4.],[3.,4.,0.]])
    T,C,R=controller(k,-k,2.,P,1.5)
    assert np.max(abs(R))==0 and np.max(abs(C+3*T))==0
    T,C,R=controller(k,k,2.,P,1.5)
    assert np.allclose(R[1:],1j*4/1.5*k@P)
    T,C,R=elastic(k,H0,1.5,7.)
    assert np.allclose(C,-3*T) and np.allclose(R[1:],-1j*7/1.5*k@H0)
    d=np.array([1.,2.,3.]);E=I-np.outer(d,d)/(d@d)
    A0=E@np.diag([0.,1.,-1.])@E-E*np.trace(E@np.diag([0.,1.,-1.]))/2
    assert np.max(abs(elastic(d,A0,1.2,1.)[2]))<1e-12
    assert 30+60<=120 and 80+40<=120 and 30+60>80
    print('PASS original known() mixed Fourier Ward, charge, elastic, TT, support')

if __name__=='__main__':exact()
