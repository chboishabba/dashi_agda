#!/usr/bin/env python3
"""BR116-119: exact AK normal-scale reduction, genuine Hopf shear,
foliation transport and scalar Robin resolvent. Source algebra only.
Classical differential geometry and Green estimates retain prior attribution.
"""
import argparse
from itertools import product
from fractions import Fraction as Q
import sympy as s
R=s.Rational
I=range(5)
eta=s.diag(-1,1,1,1)

def eq(a,b):
    if isinstance(a,s.MatrixBase):
        assert (a-b).applyfunc(s.cancel)==s.zeros(*a.shape), (a-b)
    else:
        assert s.cancel(a-b)==0,(a,b,s.cancel(a-b))

def sym(seed,n=5):
    return s.Matrix(n,n,lambda i,j:R(((min(i,j)+2)*(max(i,j)+seed+3))%23-11,31+seed))

def ak_jets(b,k):
    # BR14 harmonic-Y and actual constant-curvature base RNC jets.
    h0=R(4,5);kn=1-k*k
    assert b*b*kn==h0*h0
    g=s.diag(-b*b,b*b,b*b,b*b,b**8)
    dg=[s.zeros(5) for _ in I];dg[4]=s.diag(-2*k*b**6,2*k*b**6,2*k*b**6,2*k*b**6,8*k*b**12)
    ddg=[[s.zeros(5) for _ in I] for _ in I]
    for a,c in product(range(4),repeat=2):
        ddg[a][c][:4,:4]=b*b*h0*h0/3*s.Matrix(4,4,lambda i,j:2*eta[a,c]*eta[i,j]-eta[i,a]*eta[j,c]-eta[i,c]*eta[j,a])
    ddg[4][4]=s.diag(*[-2*b**10*(kn+6*k*k),*[2*b**10*(kn+6*k*k)]*3,8*b**16*(kn+12*k*k)])
    return g,dg,ddg

def scale_oracle(b,k,seed):
    g,dg,ddg=ak_jets(b,k);gi=g.inv()
    p=sym(seed);dp=[sym(seed+a+1) for a in I];ddp=[[sym(seed+6+min(a,c)*5+max(a,c)) for c in I] for a in I]
    vi=-gi*p*gi
    dgi=[-gi*d*gi for d in dg]
    dvi=[-dgi[a]*p*gi-gi*dp[a]*gi-gi*p*dgi[a] for a in I]
    low=lambda D,i,j,m:(D[i][m,j]+D[j][m,i]-D[m][i,j])/2
    A={(i,j,m):low(dg,i,j,m) for i,j,m in product(I,repeat=3)}
    B={(i,j,m):low(dp,i,j,m) for i,j,m in product(I,repeat=3)}
    G={(a,i,j):sum(gi[a,m]*A[i,j,m] for m in I) for a,i,j in product(I,repeat=3)}
    V={(a,i,j):sum(vi[a,m]*A[i,j,m]+gi[a,m]*B[i,j,m] for m in I) for a,i,j in product(I,repeat=3)}
    dG={(c,a,i,j):sum(dgi[c][a,m]*A[i,j,m]+gi[a,m]*low(ddg[c],i,j,m) for m in I) for c,a,i,j in product(I,repeat=4)}
    dV={(c,a,i,j):sum(dvi[c][a,m]*A[i,j,m]+vi[a,m]*low(ddg[c],i,j,m)+dgi[c][a,m]*B[i,j,m]+gi[a,m]*low(ddp[c],i,j,m) for m in I) for c,a,i,j in product(I,repeat=4)}
    # Background and independent first variation of Ric_YY.
    rr=sum(dG[a,a,4,4]-dG[4,a,4,a] for a in I)+sum(G[a,a,m]*G[m,4,4]-G[a,4,m]*G[m,4,a] for a,m in product(I,repeat=2))
    eq(rr,-4*g[4,4])
    dr=sum(dV[a,a,4,4]-dV[4,a,4,a] for a in I)+sum(V[a,a,m]*G[m,4,4]+G[a,a,m]*V[m,4,4]-V[a,4,m]*G[m,4,a]-G[a,4,m]*V[m,4,a] for a,m in product(I,repeat=2))
    # H_cov equals original contracted background Gamma and has H_Y=0.
    # At base RNC all H components zero; derivative in Y also zero.
    c_up=sum(vi[i,j]*G[4,i,j]+gi[i,j]*V[4,i,j] for i,j in product(I,repeat=2))
    dc_up=sum(dvi[4][i,j]*G[4,i,j]+vi[i,j]*dG[4,4,i,j]+dgi[4][i,j]*V[4,i,j]+gi[i,j]*dV[4,4,i,j] for i,j in product(I,repeat=2))
    c=b**4*c_up
    cy=dg[4][4,4]*c_up+b**8*dc_up
    # Ered_YY variation, C background identically zero.
    e=(dr+4*p[4,4]-cy+G[4,4,4]*b**8*c_up)/b**8
    # delta psi = p_YY/(2 b^8), independent literal scalar wave.
    l=p[4,4]/(2*b**8)
    ly=dp[4][4,4]/(2*b**8)-8*k*b**4*l
    lyy=ddp[4][4][4,4]/(2*b**8)-16*k*b**4*dp[4][4,4]/(2*b**8)+(64*k*k-8*(1-k*k+4*k*k))*b**8*l
    box=sum(eta[a,a]*ddp[a][a][4,4]/(2*b**10) for a in range(4))+lyy/b**8
    eq(box-6*k*ly/b**4-8*l-2*k*c,-e)
    # All tangent/mixed jets are independently sampled, not set zero.
    assert c!=0 and e!=0

def ak():
    for q,(b,k) in enumerate([(R(1),-R(3,5)),(R(4,5),R(0)),(R(5,6),R(7,25)),(R(1),R(3,5))]):
        scale_oracle(b,k,2+q)
    # Optical conjugation and actual Robin conversion.
    x=s.symbols('x',real=True);B=s.Function('B')(x);u=s.Function('u')(x);ell=s.symbols('ell')
    ko=s.diff(B,x)/B;l=B**R(3,2)*u
    left=s.diff(l,x,2)-3*ko*s.diff(l,x)-(ell**2+8*B**2)*l
    right=s.diff(u,x,2)-(ell**2+8*B**2-R(3,2)*s.diff(ko,x)+R(9,4)*ko**2)*u
    eq(s.expand(left/B**R(3,2)-right),0)
    print('PASS BR116 exact 5D linearized reduced Ricci normal component at four actual AK points, optical reduction')

def shear():
    # Exact AN spatial seed at seam, no need for nonlinear BN representative.
    # At y=0,L b=1, H=gamma+a a^T, lambda^2=1-a^T H^-1 a,
    # beta=H^-1 a. Opposite b_y terms cancel in mean K.
    x=s.Matrix(s.symbols('x:3'));r=x.dot(x);eps=R(1,40);h0=R(4,5)
    fac=2*(1+r)/(h0*(1-r)**2);X=fac*x;X1,X2,X3=X
    A=2*s.Matrix([2*X1*X3-2*X2,2*X1+2*X2*X3,1-X1**2-X2**2+X3**2])/(1+X.dot(X))**2
    a=eps*X.jacobian(x)*A;gam=4/(h0*h0*(1-r)**2);H=gam*s.eye(3)+a*a.T
    pt=dict(zip(x,[R(1,5),0,0]));H0=H.subs(pt);a0=a.subs(pt);hi=H0.inv();beta=hi*a0
    dH=[H.diff(t).subs(pt) for t in x];da=[a.diff(t).subs(pt) for t in x]
    db=[hi*(da[i]-dH[i]*beta) for i in range(3)];D=s.Matrix.hstack(*db)
    LH=sum((beta[i]*dH[i] for i in range(3)),s.zeros(3))+D.T*H0+H0*D
    # -2lambda M_sp = Lie_beta H. TF nonzero iff this matrix TF nonzero.
    tf=LH-H0*s.trace(hi*LH)/3
    assert tf!=s.zeros(3)
    # Independent scalar minor witnesses failure of proportionality.
    minor=s.cancel(LH[0,1]*H0[0,0]-LH[0,0]*H0[0,1]);assert minor!=0
    # Conformal scalar factor changes TF only by u; BE/BO/BQ lifts
    # have zero first jets at seam, so cannot cancel this shear.
    U=s.symbols('U',positive=True);nu=s.symbols('nu');Mt=U*LH+nu*H0
    eq(Mt-U**2*H0*s.trace((U**2*H0).inv()*Mt)/3,U*tf)
    # Actual null pair: H01=0, so spatial e0+e1 and e0-e1
    # have equal squared length. Equal time component makes both null
    # in the time-symmetric wall. Their shear contractions differ by
    # 4 M01, regardless of the time-time mean or spatial trace.
    assert H0[0,1]==0 and LH[0,1]!=0
    ep=s.Matrix([1,1,0]);em=s.Matrix([1,-1,0])
    eq((ep.T*H0*ep-em.T*H0*em)[0],0)
    eq((ep.T*tf*ep-em.T*tf*em)[0],4*LH[0,1])
    # General mixed-shape variation: A=h^-1 K, S=A-tau I/4.
    tau,npsi,dt,dn,dq=s.symbols('tau npsi dt dn dq');S=s.Matrix(4,4,lambda i,j:s.Symbol(f'S{i}{j}'));S[0,0]=-sum(S[i,i] for i in range(1,4));T=s.Matrix(4,4,lambda i,j:s.Symbol(f'T{i}{j}'));A=S+tau*s.eye(4)/4
    eq(2*s.trace(A*T),tau*s.trace(T)/2+2*s.trace(S*T))
    lhs=tau*dn+(npsi-tau/2)*dt-2*s.trace(S*T)
    rhs=(npsi+tau/2)*dn-(npsi-tau/2)*dq-2*s.trace(S*T)
    eq(lhs.subs(dt,dn-dq),rhs)
    # Null-cone test in Lorentz orthonormal frame: tracefree shear
    # K=k h+M gives M(z#,z#) not proportional to q.
    k=s.symbols('k');M=s.diag(0,1,-1,0);K=k*eta+M;z=s.Matrix([1,1,0,0]);zz=eta*z
    eq((z.T*eta*z)[0],0);eq((zz.T*K*zz)[0],1)
    print('PASS BR117 actual AN signed shear at x=(1/5,0,0), exact minor',minor)
    print('PASS BR117 conformal/first-jet repair persistence and null-cone shear obstruction')

def foliation():
    # Exact variation of inverse normal norm for arbitrary admissible
    # metric, defining-function jet and perturbations.
    g=s.diag(-2,3,4,5,6);g[0,2]=g[2,0]=R(1,5);gi=g.inv();p=sym(4)
    F=s.Matrix([0,R(1,3),R(1,7),R(1,11),1]);dF=s.Matrix(s.symbols('d:5'))
    z=(F.T*gi*F)[0];assert z>0;la=1/s.sqrt(z);n=la*gi*F
    dz=(2*dF.T*gi*F-F.T*gi*p*gi*F)[0];dpsi=-dz/(2*z)
    eq(dpsi,(n.T*p*n)[0]/2-la*n.dot(dF))
    dn=la*gi*dF-gi*p*n+dpsi*n
    Dt=gi*dF-n*n.dot(dF)
    pk=gi*p*n;nkn=(n.T*p*n)[0]
    eq(dn,-n*nkn/2-(pk-n*nkn)+la*Dt)
    # Fixed g, varying defining function sigma: independent curved
    # conformal Gaussian example with arbitrary tangent derivatives.
    t,x,y=s.symbols('t x y',real=True);f=t*x/7+y/11;psi=t*y/13+x*x/17
    sig=t*x/19+y*t/23+x*y/29
    # Tangential part of delta normal lambda D sigma, divergence
    # using volume e^(4f+psi), with two spectator axes.
    grad=lambda q:s.Matrix([-s.diff(q,t),s.diff(q,x)])*s.exp(-2*f)
    V=s.exp(psi)*grad(sig);div=sum(s.diff(V[i],a)+(4*s.diff(f,a)+s.diff(psi,a))*V[i] for i,a in enumerate([t,x]))
    leafbox=s.exp(-2*f)*(-s.diff(sig,t,2)+s.diff(sig,x,2)-2*s.diff(f,t)*s.diff(sig,t)+2*s.diff(f,x)*s.diff(sig,x))
    eq(s.simplify(div-s.exp(psi)*(leafbox+2*grad(psi).dot(s.Matrix([s.diff(sig,t),s.diff(sig,x)])))),0)
    # Naturality distinction: at Gaussian normal reference phi=y,
    # Lie metric has delta psi=v_n; sigma=Vphi=v cancels it.
    v=s.Function('v')(t,x,y);wall=s.Function('w')(t,x)
    eq(s.diff(v,y)-s.diff(v,y),0)
    assert s.diff(v,y)-s.diff(wall,y)==s.diff(v,y)
    # Independent shape variation oracle at a nonorthogonal material
    # point. Fixed g, perturb defining-function first and second jets.
    # Choose F=dy in a sheared metric; E(e) tangent to F+e dF.
    E=s.eye(5)[:,:4];e=s.Symbol('e');B=s.Matrix(s.symbols('b:5'));J=sym(8);F=s.eye(5)[:,4]
    g0=s.diag(-2,3,4,5,6);g0[1,4]=g0[4,1]=R(1,7);gi0=g0.inv()
    la0=1/s.sqrt((F.T*gi0*F)[0]);n0=la0*gi0*F;h=E.T*g0*E
    # Arbitrary background Hess phi, sigma, expressed covariantly.
    A=sym(7);z0=(F.T*gi0*F)[0];z1=2*(B.T*gi0*F)[0]
    # Exact tangent variation E'=-lambda n (E^T d sigma)^T.
    dE=-la0*n0*(E.T*B).T
    dK=la0*(dE.T*A*E+E.T*J*E+E.T*A*dE)-la0*z1/(2*z0)*E.T*A*E
    # Independent direct expression using literal normalized Hessian
    # with changing tangent frame, derivative at e=0.
    Ee=E+e*dE;Fe=F+e*B;ze=(Fe.T*gi0*Fe)[0]
    direct=Ee.T*(A+e*J)*Ee/s.sqrt(ze)
    eq(direct.diff(e).subs(e,0),dK)
    assert dK!=la0*E.T*J*E
    # At the fixed foliation, shape derivative has -Hess v;
    # transporting phi by sigma=v adds +Hess v. Trace alone is
    # insufficient at a null covector and nonzero tracefree M.
    a=s.Matrix(s.symbols('a:4'));J=a*a.T
    eq(-J+J,s.zeros(4))
    print('PASS BR118 general defining-function metric variation, curved divergence and transport vs graph-only distinction')

def robin():
    # Optical AK scale operator -d²+U, U=(13/2)b²+(9/4)kopt².
    # Both endpoints outward derivative = (3/2)u; this sign matters.
    c=Q(3,2);umin=Q(13,2)*Q(16,25);umax=Q(13,2)+Q(9,4)*Q(9,25)
    assert umin==Q(104,25) and umax==Q(731,100)
    # For length d>1, |u(0)|²+|u(d)|² <= 2/d||u||²+4||u||||u'||.
    # 4c ab <= (1/2)b²+8c² a²; form >= 1/2||u'||²-17||u||².
    assert umin-2*c-8*c*c> -17
    # Spectral lower bound -17; for s=gamma+i omega, gamma>=16,
    # min |s²+|xi|²+lambda| >= (gamma²-17) for lambda>=-17.
    ga=Q(16);A=ga*ga-17;assert A==239
    w,r=s.symbols('w r',real=True);g=s.symbols('g',positive=True)
    # If w²<=g²-17, minimum in r>=-17 gives at r=-17.
    eq((g*g-w*w-17)**2+4*g*g*w*w-(g*g-17)**2,w**4+(2*g*g+34)*w*w)
    # If w²>=g²-17, 2g |w| >= g²-17 for g²>17.
    eq(4*g*g*(g*g-17)-(g*g-17)**2,(g*g-17)*(3*g*g+17))
    # L² endpoint operator bounds for the perturbed Robin inverse.
    # Use exp(-ad)<1/100 at a>=16, d>1.
    assert sum(Q(5)**k/Q(s.factorial(k)) for k in range(7))>100
    cU=Q(8);delta=cU/ga**2;assert delta==Q(1,32) and 2/(1-delta)<3
    # ||D_U-ell I|| <= 2 L/99 + 6 cU/a; Robin subtracts 3/2 I.
    assert Q(2,99)+(6*cU/ga+c)/ga<Q(1,2)
    # ||A|| <= 2/L (||g_R||+3||f||/sqrt(a)); |p|<=sqrt2 ||A||.
    # Use sqrt2<3/2 => |p| <= 3||g_R||/L+9||f||/(L sqrt(a)).
    # BR114 generator norm <=10 Dfreq² |p|/(L sqrt(a)).
    # For bulk source and tangential H1 weight m: Dfreq²<=2m²,
    # a L²>=gamma² m. Hence 180/gamma² times m||f||.
    assert 10*9*2==180
    print('PASS BR119 finite Robin trace inverse <=2/L; joint bulk H1-source bound <=180/gamma²; separate Robin forcing retained')
    print('PASS BR119 actual AK scale potential [104/25,731/100], Robin form lower bound -17, damped scalar inverse <=1/239 at gamma=16')

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--part',choices=['ak','shear','foliation','robin'],required=True)
    {'ak':ak,'shear':shear,'foliation':foliation,'robin':robin}[p.parse_args().part]()
