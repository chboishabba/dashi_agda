"""BL: exact rational global energy Schur certificate.
Inputs: AN radial norm certificates and projected BG scalar jet envelopes.
All tensor inequalities and norms are specified in the BL parent roadmap.
"""
from fractions import Fraction as F
from math import isqrt

def rt(x):
    # outward sqrt using exact integer arithmetic, step 1e-12
    x=F(x);N=10**12; k=isqrt((x.numerator*N*N)//x.denominator)
    return F(k+1,N)

def run(w=F(2602,10**6),wx=F(14251,10**6),wy=F(12675,10**6)):
    A=F(13,250);B=F(29,200);C2=F(49,100)
    divA=F(13,100) # certified separately by original AN radial polynomial
    h=F(4,5);J=F(6,5);beta=F(3,5);f=F(7,200);fp=F(7,40);sqrt3=rt(3)
    umax=1/(1-w);umin=1/(1+w);du=umax-1;S=1+A*A;da=A*B
    Hder=2*A*B
    M=B*(1+2*A*A);Md=da*M+C2+4*A*B*B+2*A*A*C2
    def tf(x,dx):return S*x,S*dx+sqrt3*(S+1)*Hder*x/3
    MT,MTd=tf(M,Md)
    a2=B*B+A*C2+3*da*da;X,Xd=tf(da*A,a2*A+da*B)
    C0=J*(X+MT);C0d=J*(Xd+MTd+3*da*MT)
    C1=F(3,2)*J*MT;C1d=F(3,2)*J*(MTd+2*da*MT)
    P=(1-h*h)*A*A*sqrt3/2+A*A+f*(C0+du*C1)
    Px=(1-h*h)*sqrt3*da+(1-h*h)*da*A*A+2*A*B+f*(C0d+du*C1d+umax*umax*wx*C1)
    Py=2*beta*(sqrt3*A*A/2+A*A)+fp*(C0+du*C1)+f*umax*umax*wy*C1
    Qerr=P-h*h*A*A # replace aa term A² by (1-b²)A²
    ks=P/h**2+A/h;kg=max(umax**2*(1+ks)-1,1-umin**2*(1-ks));assert ks<1 and kg<1
    # Reference-lowered connection difference K of the seed.
    K=rt((sqrt3*beta*A/h+F(3,2)*Px/h**3)**2+2*B*B/h**4+2*(Py/(2*h*h))**2+2*((Py+2*beta*P)/(2*h*h))**2+2*(beta*A/h)**2)
    TK=rt((3*beta*A/h+2*sqrt3*Px/h**3)**2+(divA/h**2+sqrt3*(beta*P+Py)/h**2)**2)
    # Convert C_seed to the actual physical frame; add conformal connection.
    # upper bound on 1/sqrt(1-ks) using sqrt of reciprocal, not inverse of upper sqrt.
    iv=rt(1/(1-ks));lg=rt(wx*wx/h**2+wy*wy)*iv
    Cg=(1+w)*rt(1+ks)*K/(1-ks)**2+rt(10)*lg
    d=umax*f*C1/(h*h*(1-ks))
    D0x=f*(C1d+3*umax*wx*C1)/h**3
    D0y=(fp+3*f*umax*wy+2*beta*f)*C1/h**2
    D0=f*C1/h**2
    d1=rt(D0x*D0x+D0y*D0y+2*beta*beta*D0*D0)*iv**3+2*d*Cg
    # The two contractions of K are retained, instead of bounding T by |C| alone.
    T=2*(1+w)*rt(1+ks)/(1-ks)*(TK+4*ks*K/(1-ks))+12*lg+4*d*Cg
    qmin=h*h-Qerr;assert qmin>0
    m=1+2*w+(1+w)*A**4/4;sQ=rt(1+A*A/qmin)
    Z=beta*m*sQ
    divZ=m*(1+w)*sQ*(1+2*beta**2+beta*(3*umax*wy+A*A*(2*beta+Py)/(2*qmin*qmin)+sqrt3*(Py+2*beta*Qerr)/(2*qmin)))
    Mlo=6-3*d;Vlo=12*(2-d)/(1+kg)-5*d1*Cg-(10+5*d)*Cg*Cg-6*divZ
    ell=4*d1+2*T+12*Z;schur=Vlo-ell*ell/(4*Mlo)
    for k,x in locals().copy().items():
        if isinstance(x,F):print(k,float(x))
    print('GLOBAL M lower',float(Mlo),'V lower',float(Vlo),'ell upper',float(ell),'Schur lower',float(schur),flush=True)
    assert Mlo>0 and schur>0
    hc=min(Mlo/2,schur/(1+2*(ell/(2*Mlo))**2))
    print('H1 coercivity lower',float(hc),'L2 inverse upper',float(1/schur),flush=True)
    print('PASS full-ball energy coercivity from exact rational norm bounds',flush=True)
    return Mlo,schur,hc

def identities():
    import sympy as s
    n=4;b,B=s.symbols('b B',positive=True);a=s.Matrix(s.symbols('a0:3'));T=s.Matrix(3,3,s.symbols('t0:9'));P=s.Matrix(3,3,s.symbols('p0:9'));P=P+P.T;Py=s.Matrix(3,3,s.symbols('y0:9'));Py=Py+Py.T
    Px=[s.Matrix(3,3,s.symbols('p'+str(i)+'_0:9')) for i in range(3)];Px=[p+p.T for p in Px]
    g=s.MutableDenseNDimArray.zeros(n,n,n)
    for i in range(3):
        for j in range(3):
            for k in range(3):g[i,j,k]=Px[i][j,k]/b**3+B*(int(i==j)*a[k]+int(i==k)*a[j])/b
            g[i,j,3]=g[i,3,j]=(T[i,j]-B*P[i,j])/b**2;g[3,i,j]=(Py[i,j]-2*B*P[i,j])/b**2
        g[i,3,3]=-2*B*a[i]/b;g[3,i,3]=g[3,3,i]=-B*a[i]/b
    K=lambda k,i,j:(g[i,j,k]+g[j,i,k]-g[k,i,j])/2
    for i in range(3):
        for j in range(3):
            assert s.expand(K(3,i,j)-(T[i,j]+T[j,i]-Py[i,j])/(2*b*b))==0
            assert s.expand(K(j,i,3)-(T[i,j]-T[j,i]+Py[i,j]-2*B*P[i,j])/(2*b*b))==0
            for k in range(3):assert s.expand(K(k,i,j)-(Px[i][j,k]+Px[j][i,k]-Px[k][i,j])/(2*b**3)-B*int(i==j)*a[k]/b)==0
        assert s.expand(K(3,i,3)+B*a[i]/b)==0 and s.expand(K(i,3,3))==0
    for k in range(4):
        v=sum(K(k,i,i)-K(i,k,i) for i in range(4))
        target=(3*B*a[k]/b+sum(Px[i][i,k]-Px[k][i,i] for i in range(3))/b**3) if k<3 else (s.trace(T)+B*s.trace(P)-s.trace(Py))/b**2
        assert s.expand(v-target)==0
    l=s.symbols('l0:4');Cf=lambda k,i,j:int(k==i)*l[j]+int(k==j)*l[i]-int(i==j)*l[k]
    assert s.expand(sum(Cf(k,i,j)**2 for k in range(4) for i in range(4) for j in range(4))-10*sum(x*x for x in l))==0
    for k in range(4):assert s.expand(2*sum(Cf(k,i,i)-Cf(i,k,i) for i in range(4))+12*l[k])==0
    z=s.symbols('z');t=z*(1-z);assert s.expand(s.diff(t*t*(1-2*z),z)-2*t*(1-5*t))==0
    assert F(139,100)**2/(25*F(223,100))<F(7,200) and F(223,100)**2<5 and F(139,100)/8<F(7,40)
    print('PASS exact mixed/tangential connection, two trace contractions, conformal norm and polynomial collar maximum',flush=True)

if __name__=='__main__':
    identities();a=run();assert a[1]>F(235,100) and a[2]>F(83,100)
    print('larger explicit C1 tube',flush=True);run(F(3,1000),F(17,1000),F(15,1000))
