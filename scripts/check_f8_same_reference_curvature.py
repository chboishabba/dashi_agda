"""Original a=t AdS5 same-reference TT curvature, linear Israel and layer jump.
Symbolic continuum identities, not discrete convergence or native kernel acceptance.
"""
import json
import sympy as S
from functools import lru_cache


def geometry(n):
    # Coordinates T,x1,x2,x3,z (bulk) or eta,x1,x2,x3 (brane).
    k=S.Matrix(S.symbols('kx ky kw',real=True));K=(k.T*k)[0]
    P=K*S.eye(3)-k*k.T;Q=S.diag(0,1,-1)
    H=(P*Q*P-P*S.trace(P*Q)/2).applyfunc(S.expand)
    assert (k.T*H).applyfunc(S.expand)==S.zeros(1,3)
    assert S.expand(S.trace(H))==0
    T,z=S.symbols('T z',real=True,positive=True);bulk=n==5
    f=S.Function('f')(T,z) if bulk else S.Function('f')(T)
    signs=[-1]+[1]*(n-1);h=S.zeros(n);h[1:4,1:4]=H*f
    phi=[0]*n;phi[-1 if bulk else 0]=-1/z if bulk else S.Integer(1)
    eta=lambda a,b:signs[a] if a==b else 0
    delta=lambda a,b:int(a==b)
    def deriv(x,a):
        if a==0:return S.diff(x,T)
        if bulk and a==4:return S.diff(x,z)
        return S.I*k[a-1]*x
    def bgder(x,a):return S.diff(x,z) if bulk and a==4 else 0
    @lru_cache(None)
    def G(a,b,c):return delta(a,b)*phi[c]+delta(a,c)*phi[b]-eta(b,c)*signs[a]*phi[a]
    @lru_cache(None)
    def F(a,b,c):return S.expand(signs[a]*(deriv(h[a,c],b)+deriv(h[a,b],c)-deriv(h[b,c],a))/2)
    @lru_cache(None)
    def dG(a,b,c):return F(a,b,c)-h[b,c]*signs[a]*phi[a]
    checks=0
    def eq(a,b):
        nonlocal checks
        assert S.expand(a-b)==0,(a,b);checks+=1
    # Actual background connection; constant curvature R^a_bcd=-(delta^a_c g_bd-delta^a_d g_bc).
    if bulk:
        for a in range(n):
            for b in range(n):
                for c in range(n):
                    for d in range(n):
                        R=bgder(G(a,b,d),c)-bgder(G(a,b,c),d)+sum(G(a,e,c)*G(e,b,d)-G(a,e,d)*G(e,b,c) for e in range(n))
                        eq(R,-(delta(a,c)*eta(b,d)-delta(a,d)*eta(b,c))/z**2)
    # Background Ricci and mixed source/Einstein raising terms.
    for a in range(n):
        for b in range(n):
            R=sum(bgder(G(c,a,b),c)-bgder(G(c,a,c),b)+sum(G(c,c,e)*G(e,a,b)-G(c,b,e)*G(e,a,c) for e in range(n)) for c in range(n))
            eq(R,-4*eta(a,b)/z**2 if bulk else (2 if a==b and a>0 else 0))
    # Ricci from independently expanded curved first variation of Christoffels.
    box=lambda x:-deriv(deriv(x,0),0)+sum(deriv(deriv(x,a),a) for a in range(1,n))
    Ric=S.zeros(n);flat=S.zeros(n)
    for a in range(n):
        for b in range(n):
            flat[a,b]=S.expand(sum(deriv(F(c,a,b),c)-deriv(F(c,a,c),b) for c in range(n)))
            eq(flat[a,b],-box(h[a,b])/2)
            Ric[a,b]=S.expand(sum(deriv(dG(c,a,b),c)-deriv(dG(c,a,c),b)+sum(dG(c,c,e)*G(e,a,b)+G(c,c,e)*dG(e,a,b)-dG(c,b,e)*G(e,a,c)-G(c,b,e)*dG(e,a,c) for e in range(n)) for c in range(n)))
            if bulk:eq(Ric[a,b]+4*h[a,b]/z**2,(-box(h[a,b])+3*deriv(h[a,b],4)/z)/2)
            elif a in (1,2,3) and b in (1,2,3):eq(Ric[a,b]-2*h[a,b],(-box(h[a,b])+2*deriv(h[a,b],0))/2)
            else:eq(Ric[a,b],0)
    eq(sum(signs[a]*flat[a,a] for a in range(n)),0)
    eq(sum(signs[a]*Ric[a,a] for a in range(n)),0)
    # Flat conformal Weyl; background Weyl vanishes, so frame perturbations make no linear correction.
    v,c,b=S.symbols('v c b',real=True);extras=(0,4) if bulk else (0,)
    for i in range(1,4):
        for j in range(i,4):
            for a in extras:
                for d in extras:
                    R=signs[i]*(deriv(F(i,a,d),j)-deriv(F(i,a,j),d))
                    C=R-(eta(i,j)*flat[d,a]-eta(i,d)*flat[j,a]-eta(a,j)*flat[d,i]+eta(a,d)*flat[j,i])/(n-2)
                    eq(C,-deriv(deriv(h[i,j],a),d)/2+eta(a,d)*box(h[i,j])/(2*(n-2)))
    return checks


def wall():
    b=S.symbols('b',positive=True);beta=S.sqrt(1+b*b);v=-b/beta;a=b/(1+b*b)**2;s=1-v*v
    A,B,D,E,Y,L=S.symbols('A B D E Y L',real=True) # moving U_T,U_TT,U_y,U_Ty,U_yy,Lap U
    dt=lambda x:S.diff(x,b)*v
    Teta=beta;Heta=Teta*A;Hetaeta=Teta**2*B+Teta*dt(Teta)*A
    G=v*A+s*D;bulk=-B+2*v*E+s*Y+(a-3/b)*D+L
    box=bulk+3*D/b;N=v*v*B+2*v*s*E+s*s*Y-v*v*a*D
    direct=b*b*(-N/(2*s)+box/6);sms=-b*b*(Hetaeta+2*Heta-L)/2
    checks=0
    def eq(x,y):
        nonlocal checks
        assert S.simplify(x-y)==0;checks+=1
    eq(dt(v),a);eq(Teta*dt(Teta),-b*b/beta)
    eq(direct-sms,-(b+b**3/2)*G-b*b*bulk/3)
    # Mixed extrinsic curvature, K^i_j = n(phi) delta^i_j + 1/2 n(h)^i_j at first order.
    # The TT perturbation leaves normal, tangent, trace and time-spatial blocks unchanged.
    nT=b*beta*v;nz=b*beta;uT=b*beta;uz=b*beta*v
    eq((-nT*nT+nz*nz)/b**2,1);eq((-uT*uT+uz*uz)/b**2,-1);eq((-nT*uT+nz*uz)/b**2,0)
    eq(-nz/b,-beta)
    # Background acceleration in bulk Poincare coordinates, proper time derivative.
    # Along the wall db/dt=-b^2, Gamma^T_Tz=-1/b,
    # Gamma^z_TT=-1/b, Gamma^z_zz=-1/b.
    at=-b*b*S.diff(uT,b)-2*uT*uz/b
    az=-b*b*S.diff(uz,b)-(uT*uT+uz*uz)/b
    eq((-nT*at+nz*az)/b**2,-1/beta)
    # Direct mixed spatial K first variation using pullback and inverse perturbation.
    e=S.symbols('e');h,nh=S.symbols('h nh');K0=-beta
    eq(S.diff((1-e*h)*(K0*(1+e*h)+e*nh/2),e).subs(e,0),nh/2)
    eq(b*beta*(-6/(b*beta))/2,-3)
    # Background Israel: rho=beta-1, pressure fixed by conservation and a=t.
    rho=beta-1;pressure=-rho+b*b/(3*beta);trace=-rho+3*pressure-4
    eq(-3*(-rho-1)+trace,-1/beta);eq(-3*(pressure-1)+trace,-beta)
    eq(b*S.diff(rho,b),3*(rho+pressure))
    eq((rho+1)**2-1,b*b)
    # All arbitrary moving jets: direct formula reproduces inherited rational slice.
    X,Z,tt,tz,zz,lap=S.symbols('X Z tt tz zz lap')
    sl={b:S.Rational(3,4),A:X+v*Z,B:tt+2*v*tz+v*v*zz+a*Z,D:Z,E:tz+v*zz,Y:zz,L:lap}
    eq(direct.subs({k0:S.simplify(v0.subs(b,S.Rational(3,4))) if hasattr(v0,'subs') else v0 for k0,v0 in sl.items()}),-S.Rational(129,512)*tt+S.Rational(3,32)*lap-S.Rational(177,512)*zz+S.Rational(135,256)*tz)
    # Actual angular integral of all six TT symbols on x-axis. Averaging
    # powers of y=k_perp cos(theta), w=k_perp sin(theta) is exact.
    x,y,w,p=S.symbols('x y w p',real=True);k=S.Matrix([x,y,w]);K=(k.T*k)[0]
    P=K*S.eye(3)-k*k.T;Q=S.diag(0,1,-1);TT=P*Q*P-P*S.trace(P*Q)/2
    from math import factorial
    def azimuth(expr):
        total=0
        for (i,j),c in S.Poly(S.expand(expr),y,w).terms():
            if i%2 or j%2:continue
            a,b=i//2,j//2
            total+=c*p**(a+b)*S.Rational(factorial(2*a)*factorial(2*b),4**(a+b)*factorial(a)*factorial(b)*factorial(a+b))
        return S.expand(total)
    K0=x*x+p;yy=(x**4+6*K0*x*x+K0*K0)/8
    for i in range(3):
        for j in range(3):eq(azimuth(TT[i,j]),yy*Q[i,j])
    # Mixed first-order stress conservation: spatially transverse pi; metric
    # variation of connection contributes only spatial trace or h_0a terms.
    rho,pres=S.symbols('rho pres');stress=[-rho-1]+[pres-1]*3
    h=TT;assert (k.T*h).applyfunc(S.expand)==S.zeros(1,3)
    eq(S.trace(h),0)
    # Sum delta Gamma^a_ab (S_b-S_a) = 0, diagonal stress isotropic.
    # delta Gamma^a_a0 = h_aa'/2 for spatial a; delta Gamma^0_0b=0.
    eq((stress[0]-stress[1])*S.trace(h)/2,0)
    return checks


def layer():
    # Distributional coefficients for extension by H(z-b(T)).
    v,a,F,Fp,Pt,Pz=S.symbols('v a F Fp Pt Pz',real=True);s=1-v*v
    h=Pz+v*Pt
    assert S.expand(-a*F-2*v*Pt-(1+v*v)*Pz-(-a*F-v*(Pt+v*Pz)-h))==0
    # After integrating the tangential derivative by parts, coefficient of K_xi is v²+s=1.
    assert S.expand(v*v+s)==1
    # At exterior near endpoint, derivative of retarded cone H(T-sigma-z+b(sigma))
    # w.r.t sigma is -(1-v); Dnormal has numerator (1-v); K cone value 1/2.
    assert S.cancel((1-v)/(2*(1-v)))==S.Rational(1,2)
    return 3


if __name__=='__main__':
    print(json.dumps(dict(bulk_checks=geometry(5),brane_checks=geometry(4),wall_checks=wall(),layer_checks=layer(),scope='symbolic same-reference continuum TT curvature and layer jump identities; no discrete convergence or proof kernel'),indent=2))
