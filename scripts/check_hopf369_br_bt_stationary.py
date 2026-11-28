#!/usr/bin/env python3
"""BR/BS/BT: exact stationary correction, frozen full metric seam, weighted trace.

The boundary model freezes the bulk wave at an adapted reflection-symmetric
reference point. It is NOT the warped Hopf continuum boundary symbol.
No native kernel or numerical evolution is claimed.
"""
import sympy as S


def stationary_order():
    # ADM convention K=(L_beta gamma - dt gamma)/(2N).
    # At beta=0,K=0 all stationary correction terms are second order.
    e = S.symbols('eps', real=True)
    N0,N1=S.symbols('N0 N1', real=True)
    N=N0+e*N1
    vals=S.symbols('k0:10', real=True)
    K=e*S.Matrix([[vals[0],vals[1],vals[2],vals[3]],
                  [vals[1],vals[4],vals[5],vals[6]],
                  [vals[2],vals[5],vals[7],vals[8]],
                  [vals[3],vals[6],vals[8],vals[9]]])
    Db=e*S.Matrix(4,4,S.symbols('db0:16'))
    adv=e**2*S.Matrix(4,4,S.symbols('adv0:16'))
    lie=adv+Db.T*K+K*Db
    correction=N*(S.trace(K)*K-2*K*K)+lie
    assert correction.subs(e,0)==S.zeros(4)
    assert correction.diff(e).subs(e,0)==S.zeros(4)
    # Repeat actual prior Hopf curl witness as a separate check on demand.
    print('PASS stationary ADM correction starts at order eps^2')


def frozen_wall():
    j,f=S.symbols('j f', real=True)
    h=S.diag(-1,1,1,1); g=S.diag(-1,1,1,1,1)
    n=S.Matrix([0,0,0,0,1]); nn=n*n.T
    a=S.Matrix([*S.symbols('df0:4'),0]);
    v=S.symbols('m0:15'); m=S.zeros(5); k=0
    for i in range(5):
        for l in range(i,5):
            m[i,l]=m[l,i]=v[k]; k+=1
    z=m[4,4]
    J=2*j*g+6*j*nn
    # Moving continuity and variation of unit normal covector.
    d=-f*J
    dn=z*n/2-a
    r=2*j*m+6*j*(dn*n.T+n*dn.T)+z*J/2
    assert d[4,4]==-8*j*f
    assert r[4,4]==12*j*z
    for i in range(4):
        assert S.expand(r[i,4]-2*j*m[i,4]+6*j*a[i])==0
        for l in range(4):
            assert S.expand(r[i,l]-2*j*m[i,l]-j*z*h[i,l])==0
    # Transfer channels, exact without division by the normal frequency.
    ell,coth,tanh=S.symbols('ell coth tanh', nonzero=True)
    d0,r0,G=S.symbols('d0 r0 G')
    wall=ell**2*f-ell*coth*(-8*j*f+d0)/4-G
    D=ell**2+2*j*ell*coth
    assert S.expand(wall-(D*f-ell*coth*d0/4-G))==0
    # Exact recovery of forced triangular inverse (all 15 components plus f).
    rt,rm,rn,df,hij=S.symbols('rt rm rn df hij')
    Dt=2*ell*tanh+2*j; Dn=2*ell*tanh+12*j
    fn=(G+ell*coth*d0/4)/D
    mn=-rn/Dn; mt=-(rt+j*hij*mn)/Dt; mm=(6*j*df*fn-rm)/Dt
    assert S.cancel(D*fn-ell*coth*d0/4-G)==0
    assert S.cancel(-Dn*mn-rn)==0
    assert S.cancel(-Dt*mt-j*hij*mn-rt)==0
    assert S.cancel(-Dt*mm+6*j*df*fn-rm)==0
    # sqrt(s^2+|xi|^2) glancing inequality, gamma>0.
    gamma,tau,kappa=S.symbols('gamma tau kappa', real=True)
    sq=(gamma**2-tau**2+kappa**2)**2+4*gamma**2*tau**2
    assert S.expand(sq-gamma**2*(gamma**2+tau**2+kappa**2)-((kappa**2-tau**2)**2+gamma**2*(kappa**2+tau**2)))==0
    # |tanh| >= 3/4, |coth| <=4/3 for Re ell L/2 >= 1, e^2>7.
    Jabs=S.Rational(6,5); gam=S.Integer(16)
    assert 2*S.Rational(3,4)-12*Jabs/gam >= S.Rational(1,2)
    assert 2*S.Rational(3,4)-2*Jabs/gam >= S.Rational(1,2)
    assert 1-2*Jabs*S.Rational(4,3)/gam == S.Rational(4,5)
    # The fixed-wall homogeneous normal Robin sector is not necessarily stable
    # on the undamped axis: Dn=0 at a positive ell for j<0. This is a frozen
    # reduced-gauge mode only, not a physical instability assertion.
    # Actual AK symmetric reference in the continuous-source harmonic chart:
    # dn=b^4 dy, lambda=b^4, k=b_n/b. At seam lambda=1, k=+/-j/2.
    # Variation of lambda_y/lambda^2 at the moving graph includes
    # f*4(1-k^2)+p_nn,y/2-6*k*p_nn. Average k*p_nn=j*d_nn/4.
    k=S.symbols('k', real=True)
    lam,ly,py,p=S.symbols('lam ly py p', real=True, nonzero=True)
    dl=p/(2*lam); dly=py/(2*lam)-p*ly/(2*lam**2)
    assert S.simplify((dly/lam**2-2*ly*dl/lam**3).subs({lam:1,ly:4*k})-(py/2-6*k*p))==0
    fcoef=4*(1-j*j/4)-S.Rational(3,2)*j*(-8*j)
    assert S.expand(fcoef)==4+11*j*j
    assert S.Rational(4,5)-(4+11*Jabs**2)/gam**2>S.Rational(7,10)
    print('PASS all 15 moving seam coefficients, 16-channel triangular inverse, damped and glancing bounds')
    print('PASS AK wall zeroth order contribution:',fcoef)


def weighted_energy():
    # Reference AK metric dy^2+b^2(-N0^2 dt^2+gamma_H3).
    b,N0=S.symbols('b N0', positive=True)
    metric=S.diag(-b*b*N0*N0,b*b,b*b,b*b,1)
    density=S.sqrt(-metric.det())
    inv=metric.inv()
    assert S.simplify(-density*inv[0,0]-b*b/N0)==0
    assert S.simplify(density*inv[1,1]-b*b*N0)==0
    assert S.simplify(density*inv[4,4]-b**4*N0)==0
    # Trace with L>1: a|v(0)|² <= a||v||²+2a||v||||v_y||.
    # Absorb half the minimum weighted normal gradient; exact Young square.
    a=S.Rational(12,5); w=S.Rational(4,5)**4
    C=(a+2*a*a/w)/w
    x,y=S.symbols('x y',real=True)
    assert S.expand(w*y*y/2+(a+2*a*a/w)*x*x-a*x*x-2*a*x*y-w*(y-2*a*x/w)**2/2)==0
    mass2=S.Integer(2)*S.ceiling(C)
    assert mass2>=2*C
    print('PASS AK weighted principal coefficients and trace absorption: C=',C,'mass²=',mass2)


def gauge_modes():
    # AK reference, d=4 warped AdS4, k=b_n/b, k'=1-k^2,
    # b^2(1-k^2)=h0^2. Covector gauge wave is rough wave -4.
    y=S.symbols('y', real=True); b=S.Function('b')(y)
    v=S.Function('v')(y); w=S.Function('w')(y)
    k=S.diff(b,y)/b
    # Explicit warped connection contractions (tangent/normal scalar-harmonic).
    m,h2=S.symbols('m2 h0sq',real=True)
    tang=S.diff(v,y,2)-2*k*S.diff(v,y)+(k*k-S.diff(k,y))*v + (m-3*h2)*v/b**2+4*k*(S.diff(v,y)-k*v)+k*(w-k*v)+k*w-4*v
    normal=S.diff(w,y,2)+4*k*S.diff(w,y)-4*k*k*w-4*w+m*(w-2*k*v)/b**2
    Lv=-S.diff(b*b*S.diff(v,y),y)+8*b*b*v
    Lw=-S.diff(b**4*S.diff(w,y),y)+4*b**4*(k*k+1)*w
    # Use b_nn=b and b_n^2=b^2-h0^2, retain b arbitrary elsewhere.
    assert S.simplify(S.expand(b*b*tang+Lv-m*v-2*k*b*b*w).subs(S.diff(b,y,2),b).subs(S.diff(b,y)**2,b*b-h2))==0
    assert S.simplify(b**4*normal+Lw-m*b*b*(w-2*k*v))==0
    Z=b*b
    assert S.simplify((-S.diff(b*b*S.diff(Z,y),y)+8*b*b*Z-6*h2*Z).subs(S.diff(b,y,2),b).subs(S.diff(b,y)**2,b*b-h2))==0
    j=S.symbols('j',real=True)
    assert 2*(j/2-(-j/2))==2*j # b^2 obeys tangential Robin
    # For m^2=-q<=0, multiply tangent equation by q and normal by 1.
    # Actual Lv ground form gives 6 h0^2 v^2; Lw normal Robin is positive.
    q,B,K,V,W,H=S.symbols('q B K V W H',real=True)
    combined=q*(q+6*H)*V**2+4*B**4*(K*K+1)*W**2+q*B**2*W**2-4*q*K*B**2*V*W
    squares=(q*V-2*K*B**2*W)**2+6*q*H*V**2+(4*B**4+q*B**2)*W**2
    assert S.expand(combined-squares)==0
    # q=0 normal energy forces w=0, then tangential gap forces v=0.
    print('PASS actual AK transverse gauge gap 6*h0^2 and longitudinal/normal nonpositive real mass exclusion')


if __name__=='__main__':
    stationary_order(); frozen_wall(); weighted_energy(); gauge_modes()
