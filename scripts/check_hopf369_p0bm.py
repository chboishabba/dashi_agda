"""BM: nonlinear two-state monotonicity in a fixed physical measure.
The BL bound is for a moving test/measure. This checker pays the transport
error in a convex C1 neighborhood of the actual projected trial.
"""
from fractions import Fraction as F
from check_hopf369_p0bl_coercive import rt
import sympy as s

def certify():
    # BL4 certified center and BL10 uniform wider tube, rounded outward.
    w,wx,wy=F(3,1000),F(17,1000),F(15,1000)
    w0,x0,y0=F(2602,10**6),F(14251,10**6),F(12675,10**6)
    r,rx,ry=w-w0,wx-x0,wy-y0
    U=1/(1-w);u=1/(1+w);h=F(4,5)
    kg=F(87,1000);qmin=F(631,1000);A=F(52,1000);B=F(145,1000)
    C1=F(264,1000);C1d=F(908,1000);f=F(35,1000);fp=F(175,1000)
    Px=F(42,1000);Py=F(38,1000);beta=F(3,5)
    # Metric ratio w.r.t. g0. Bounds uniform for both fixed center and path.
    # Derivatives of u-u_* are computed using u=(1+w)^-1, no Hessian.
    du=U*U*r
    dux=U*U*rx+2*U**3*r*x0
    duy=U*U*ry+2*U**3*r*y0
    R=du*f*C1;Rx=dux*f*C1+du*f*C1d;Ry=duy*f*C1+du*fp*C1
    Qx=Px+2*A*B;Qy=2*beta*rt(3)+Py
    detx=rt(3)*Rx/qmin+R*Qx/qmin**2
    dety=rt(3)*Ry/qmin+R*Qy/qmin**2
    logx=U*rx+du*x0;logy=U*ry+du*y0
    ax=5*logx+detx/2;ay=5*logy+dety/2
    k=rt((ax/h)**2+ay**2)*rt(1/(1-kg))
    Mlo=F(5952,1000);Mhi=F(6048,1000)
    Vlo=F(7545,1000);ell=F(11465,1000);V1=4*F(143,1000);T=F(1818,1000);Z=F(605,1000)
    Vfixed=Vlo-k*(V1+T+6*Z);lfixed=ell+Mhi*k
    schur=Vfixed-lfixed*lfixed/(4*Mlo)
    hc=min(Mlo/2,schur/(1+2*(lfixed/(2*Mlo))**2))
    # v=u eta, metric g vs fixed g_*. Transport both H1 terms.
    metric_ratio=(1+kg)/(1-kg);lg=F(272,10000)
    cost=max(2*metric_ratio/u**2,(1+2*metric_ratio*lg**2)/u**2)
    gamma=hc*(u/U)/cost
    for name,val in [('r',r),('rx',rx),('ry',ry),('log_a_gradient',k),('fixed_V_lower',Vfixed),('fixed_ell_upper',lfixed),('fixed_Schur',schur),('fixed_H1_local',hc),('fixed_H1_global',gamma)]:print(name,float(val),flush=True)
    assert schur>F(3,2) and gamma>F(1,5)
    return gamma

def exact():
    u,v,ax,dx,M,ell,V,K=s.symbols('u v ax dx M ell V K',real=True)
    # BL flux U=-v M dv-v²K; weighting by a gives -dlog(a) U.
    flux=-v*M*dx-v*v*K
    assert s.expand(M*dx**2+v*ell*dx+V*v*v-ax*flux-(M*dx**2+v*(ell+M*ax)*dx+(V+ax*K)*v*v))==0
    w,z,dw,dz=s.symbols('w z dw dz',real=True)
    U=1/(1+w);Uz=1/(1+z)
    assert s.cancel(U-Uz+U*Uz*(w-z))==0
    assert s.cancel(U*dw-Uz*dz-(U*(dw-dz)+(U-Uz)*dz))==0
    # determinant derivative identity for arbitrary invertible matrices is
    # Jacobi's formula; verify resolvent identity after multiplying out.
    A=s.MatrixSymbol('A',3,3);B=s.MatrixSymbol('B',3,3)
    assert (A*(A.I-B.I)*B-(B-A)).doit().expand()==s.ZeroMatrix(3,3)
    print('PASS weighted flux, reciprocal and resolvent identities',flush=True)

if __name__=='__main__':exact();certify()
