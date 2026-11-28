"""Original F8 source-representative audit and low radial mode bias diagnostic.
Uses the original two source owners and literal active radial FV coefficients.
Independent strong-incoming upwind normal comparator, NOT original mode3 RK
or certified continuum quadrature/tail. No CI or physical promotion.
"""
import json, math
import numpy as np
import sympy as S
from scipy.linalg import eigh_tridiagonal
from numba import njit
from ksw668_f8_fv_source_flux import exact_cell_averages
from ksw668_f8_weak_source import weak_source


def radial(d,n,h):
    j=np.arange(n,dtype=float);lo=np.maximum(j-.5,0);hi=j+.5
    den=hi**d-lo**d;V=h**d*den/d
    cp=d*hi**(d-1)/den;cm=d*lo**(d-1)/den
    cp[0]=2*d;cm[0]=0
    diag=(cp+cm)/h**2;off=-cp[:-1]*np.sqrt(V[:-1]/V[1:])/h**2
    np.testing.assert_allclose(off,-cm[1:]*np.sqrt(V[1:]/V[:-1])/h**2,rtol=2e-13,atol=1e-10)
    return V,diag,off


def exact():
    x=S.symbols('x');rows=[];checks=0
    for d in (3,7,11):
        V0=S.Rational(1,2)**d/d;V1=(S.Rational(3,2)**d-S.Rational(1,2)**d)/d
        r0=S.integrate(x**(d-1)*(1-x*x),(x,0,1))/V0
        r1=(S.integrate(x**(d-1)*x*x,(x,0,1))+S.integrate(x**(d-1)*(4-x*x)/3,(x,1,2)))/V1
        assert r0==S.Rational(2**(d+1),d+2);checks+=1
        assert r0!=r1;checks+=1
        rows.append(dict(d=d,R0=str(r0),R1=str(r1),K_origin_factor=str(2*d*(r0-r1))))
    assert rows[0]['K_origin_factor']=='160/13';checks+=1
    # Exact FV origin source profile of original weak monopole.
    assert S.Rational(8,5)*(-15)==-24;checks+=1
    # Incoming characteristic boundary conditions in both normal geometries.
    v,W,G=S.symbols('v W G');a,c=1+v,1-v;s=a*c
    q=(G-v*W)/s
    assert S.simplify((a*(W+c*q)-c*(W-a*q))/2-G)==0;checks+=1
    q=(W-G)/c;assert S.simplify(W-c*q-G)==0;checks+=1
    q=(G-W)/a;assert S.simplify(W+a*q-G)==0;checks+=1
    # second derivative at the outgoing endpoint, cubic reproduction.
    for k in range(4):
        assert sum(w*j**k for j,w in enumerate((2,-5,4,-1)))==(2 if k==2 else 0);checks+=1
    return dict(checks=checks,origin=rows)


def source_audit():
    rows=[]
    for n in (32,64,128,256,512,1024):
        h=1/n;r=np.arange(n+4)*h
        cell=exact_cell_averages(1.,r,h)[:,:-1];weak=weak_source(1.,r,h)[:,:-1]
        for i,d in enumerate((3,7,11)):
            V,diag,off=radial(d,len(r)-1,h);z=np.sqrt(V)*weak[i]
            kz=diag*z;kz[:-1]+=off*z[1:];kz[1:]+=off*z[:-1]
            rows.append(dict(d=d,n=n,weak_l2=float(np.linalg.norm(z)),weak_cell_l2=float(np.linalg.norm(np.sqrt(V)*(weak[i]-cell[i]))),weak_K_l2=float(np.linalg.norm(kz)),weak_h2_K0=float(h*h*kz[0]/np.sqrt(V[0]))))
    assert abs(rows[-3]['weak_h2_K0']+3840/13)<.1
    return rows


@njit
def clock(t):return np.arcsinh(t)-np.sqrt(1+t*t)/t


@njit
def coeff(T):
    t=max(1.,np.exp(T+1)/2)
    for _ in range(7):t=max(.5,t-(clock(t)-T)/(np.sqrt(1+t*t)/t**2))
    b=1/t;v=-1/np.sqrt(1+t*t);ds=T-clock(1.);q=2*ds/.065-1
    G=-6*np.sqrt(1-v*v)/b*np.exp(1-1/(1-q*q)) if 0<ds<.065 else 0.
    return b,v,G


@njit
def rhs(X,Y,h,k,T,drive):
    b,v,G=coeff(T);G*=drive;a,c=1+v,1-v;n=X.shape[1]-1
    # Strong incoming physical and alternating traces, separately from original SAT.
    X[1,n]=0.;X[2,0]=(a*X[1,0]-2*G)/c
    X[4,0]=(2*X[1,0]-5*X[1,1]+4*X[1,2]-X[1,3])/(4*h*h)
    X[5,n]=(2*X[2,n]-5*X[2,n-1]+4*X[2,n-2]-X[2,n-3])/(4*h*h)
    for o in (0,3):
        reverse=o==3
        for j in range(n+1):
            u,p,m=X[o,j],X[o+1,j],X[o+2,j]
            F=-k*k*u-3*(p-m)/(2*(b+j*h))
            Y[o,j]=(a*p+c*m)/2
            if not reverse:
                dp=(-3*p+4*X[o+1,j+1]-X[o+1,j+2])/(2*h) if j<n-1 else ((X[o+1,j+1]-p)/h if j<n else 0.)
                dm=(3*m-4*X[o+2,j-1]+X[o+2,j-2])/(2*h) if j>1 else ((m-X[o+2,j-1])/h if j>0 else 0.)
                Y[o+1,j]=a*dp+F if j<n else 0.
                Y[o+2,j]=-c*dm+F if j>0 else 0.
            else:
                dp=(3*p-4*X[o+1,j-1]+X[o+1,j-2])/(2*h) if j>1 else ((p-X[o+1,j-1])/h if j>0 else 0.)
                dm=(-3*m+4*X[o+2,j+1]-X[o+2,j+2])/(2*h) if j<n-1 else ((X[o+2,j+1]-m)/h if j<n else 0.)
                Y[o+1,j]=-a*dp+F if j>0 else 0.
                Y[o+2,j]=c*dm+F if j<n else 0.


@njit
def transfer(n,k,drive):
    h=2.01/n;T0=clock(1.);T1=clock(12.);steps=int(np.ceil((T1-T0)*(k+10/h+400)/.7));dt=(T1-T0)/steps
    X=np.zeros((6,n+1));Y=X.copy();A=X.copy();B=X.copy();integ=0.;norm=0.
    for j in range(steps):
        T=T0+j*dt
        rhs(X,Y,h,k,T,drive);A[:]=X+dt*Y
        rhs(A,Y,h,k,T+dt,drive);B[:]=.75*X+.25*(A+dt*Y)
        rhs(B,Y,h,k,T+dt/2,drive);X[:]=(X+2*(B+dt*Y))/3
        T+=dt;w=(T-T1+.15)/.1
        if abs(w)<1:
            chi=np.exp(1-1/(1-w*w));b,v,_=coeff(T)
            norm+=dt*chi;integ+=dt*chi*(-4*b*b*(1-v*v)/3)*X[3,0]
    rhs(X,Y,h,k,T1,drive)
    b,v,_=coeff(T1)
    return X[3,0],-4*b*b*(1-v*v)/3*X[3,0],integ/norm,steps


def modal():
    dr=.008;eps=.04;r=np.arange(math.ceil(3.01/dr)+1)*dr
    cell=exact_cell_averages(eps,r,dr);weak=weak_source(eps,r,dr)
    bulk=math.sqrt((clock(12.)-clock(1.))**2-(1-1/12)**2)
    out=[]
    assert transfer(128,1.,0.)[:3]==(0.,0.,0.)
    for i,d in enumerate((3,7,11)):
        V,diag,off=radial(d,len(r)-1,dr)
        lam,R=eigh_tridiagonal(diag,off,select='i',select_range=(0,3));Q=R/np.sqrt(V)[:,None]
        src=np.stack([Q.T@(V*f[i,:-1]) for f in (cell,weak)])
        receivers=[]
        for rx in (bulk-.012,bulk+.1):
            j=math.floor(rx/dr);q=rx/dr-j;ids=np.arange(j-1,j+3)
            w=np.array([-q*(q-1)*(q-2)/6,(q+1)*(q-1)*(q-2)/2,-(q+1)*q*(q-2)/2,(q+1)*q*(q-1)/6])
            receivers.append((rx/eps)**(2*i)*w@Q[ids,:])
        weights=src[:,None,:]*np.array(receivers)[None,:,:]
        for n in (256,512):
            vals=np.array([transfer(n,float(np.sqrt(k)),1.) for k in lam])
            assert np.isfinite(vals).all()
            out.append(dict(d=d,n=n,k=np.sqrt(lam).tolist(),source_coefficients=src.tolist(),signed_window_by_mode=(weights*vals[None,None,:,2]).tolist(),signed_window_partial_sum=(weights@vals[:,2]).tolist(),instant_partial_sum=(weights@vals[:,1]).tolist(),transfer=vals.tolist()))
    return out


if __name__=='__main__':
    print(json.dumps(dict(exact=exact(),sources=source_audit(),modal=modal(),scope='source-owner exact bytes, low four FV radial modes per ell, independent strong-boundary upwind normal diagnostic; not original native source-on or certified tail/sign'),indent=2))
