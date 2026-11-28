"""Original F8 radial layer weak forms and finite-band collar bounds.
No full inverse sign or omitted-band certificate. Exact rational/SymPy checks.
"""
from fractions import Fraction as Q
import json
import sympy as S


def run():
    tau,dz,v,a,b,z,x=S.symbols('tau dz v a b z x', real=True)
    q=tau*tau-dz*dz-x*x;N=dz-v*tau;L=tau-v*dz;s=1-v*v;C=N/L
    ds=lambda f:-S.diff(f,tau)-v*S.diff(f,dz)+a*S.diff(f,v)+v*S.diff(f,b)
    normal=lambda f:-v*S.diff(f,tau)-S.diff(f,dz)+S.diff(f,b)
    checks=0
    def eq(p,r):
        nonlocal checks
        assert S.cancel(p-r)==0,(p,r);checks+=1
    eq(ds(q),-2*L);eq(normal(q),2*N)
    eta=q/(4*z*b)
    eq(normal(eta)+C*ds(eta),-(1+C*v)*eta/b)
    eq(1+C*v,tau*s/L)
    eq(ds(C),(s*N-a*(tau*tau-dz*dz))/L**2)
    eq(L**2-s*(tau*tau-dz*dz),N**2)
    # Radial angular weak differentiation (polynomial moments incl odd controls).
    # M_j=int_{-1}^1 u^j / (2 pi sqrt(1-u^2)) du.
    # N_j=int sqrt(1-u^2) u^j / (4 pi) du.
    from math import comb
    for j in range(13):
        M=Q(comb(j,j//2),2*2**j) if j%2==0 else Q(0)
        k=j-2
        if k<0:rhs=Q(0)
        elif k%2:rhs=Q(0)
        else:rhs=j*(j-1)*Q(comb(k,k//2),2**k*8*(k//2+1))
        assert Q(j,2)*M==rhs;checks+=1
    e=Q(1,16);a1=Q(-15,2);a2=Q(35,8)
    # Existing transverse series: a_n positive decreasing n>=2.
    # Bounds on A', B0=3A/2-eta*A', S1=sum (n-1/2)a_n eta^(n-1).
    Ap_hi=a1+a2*(1/(1-e)**2-1)
    B0_lo=Q(3,2)+a1*e/2-a2*(e/(1-e)**2-e-Q(3,2)*e**2/(1-e))
    S1_hi=a1/2+a2*(e/(1-e)**2+e/(2*(1-e)))
    assert Ap_hi<0 and B0_lo>Q(5,4) and S1_hi<-Q(13,4);checks+=3
    A_lo=1+a1*e;assert A_lo==Q(17,32);checks+=1
    # Original wall b'=-b/sqrt(1+b^2), a=b/(1+b^2)^2. Convex wall:
    # 0<=N<= a_max*tau^2/2. Time-transfer zeroth multiplier >= 3/(2b)-a/s >=1.
    eq((1+b*b)-2*b,(b-1)**2)
    # Both collar clocks inherited from cap diamond. E: b>=.99, R: .087<b<.09.
    # E a decreasing for b>.99, bounded by a(.99)<.26; R a<b<.09.
    assert Q('.99')/(1+Q('.99')**2)**2<Q('.26');checks+=1
    collars=[]
    for name,h,bl,amax in [('E',Q('.01'),Q('.99'),Q('.26')),('R',Q('.0152'),Q('.087'),Q('.09'))]:
        Nmax=amax*h*h/2
        assert h*h/(4*bl*bl)<e;checks+=1
        assert Q(5,4)-Q(15,8)*Nmax/bl>0;checks+=1
        zer=Q(3,2)*h/bl;der=amax*h**3/12
        band=[]
        for K in (1000,2000,4000,5000):
            rho=zer+der*K*K;assert rho<1;checks+=1
            band.append(dict(k_max=K,rho_upper=str(rho),rho_display=float(rho),inverse_upper=float(1/(1-rho))))
        collars.append(dict(name=name,h=str(h),b_min=str(bl),a_max=str(amax),zeroth=float(zer),radial_second=float(der),bands=band))
    # Cross-collar N >= .7 * (2.644-.01) - 1 > .84, z<=.09.
    # The regular multiplier is strictly negative there, not a positive kernel.
    assert Q('.99')**2>Q('.7')**2/(1-Q('.7')**2);checks+=1
    Nlo=Q('.7')*(Q('2.644')-Q('.01'))-1;assert Nlo>Q('.84');checks+=1
    cross_hi=Q(3,2)-Q(13,8)*Nlo/Q('.09');assert cross_hi<0;checks+=1
    # Exact original source derivative payload positivity through two extra derivatives.
    X,Y=S.symbols('X Y');P=S.Integer(1);p=1;radial=[]
    for j in range(9):
        poly=S.Poly(S.expand((-1)**j*P.subs(X,Y+50)),Y)
        assert min(poly.all_coeffs())>0;checks+=1
        radial.append(str(min(poly.all_coeffs())))
        P=S.expand(P+2*(X*X-X)*(S.diff(P,X)-P) if p else 2*X*X*(S.diff(P,X)-P));p=1-p
    pulse=Q('.065');smax=Q('.00045');Xlo=pulse/(4*smax)
    assert 1-2*smax/pulse>Q('.98') and Xlo>36;checks+=1
    logdrive=4/pulse*Q('.98')*36**2;assert logdrive>70000;checks+=1
    # Along a fixed-lag time shift, D^2 increases, eta_dot<=2/(4 z b)+2 eta.
    # h_s >= 70000 h; A>=17/32, -A'<=15/2. Radial angular pairs nonnegative by convexity.
    eta_dot=2/(4*Q('.087')**2)+2*e;assert eta_dot<67;checks+=1
    direct_growth=70000*A_lo-Q(15,2)*eta_dot;assert direct_growth>0;checks+=1
    return dict(checks=checks,analytic_factor=dict(A_lower=str(A_lo),A_upper='1',A_prime_lower=str(a1),A_prime_upper=str(Ap_hi),B0_lower=str(B0_lo),S1_upper=str(S1_hi)),time_transfer=dict(zeroth_coefficient_lower='1',source_time_derivative_coefficient='nonnegative',explicit_potential_coefficient='nonnegative'),collars=collars,cross_regular_multiplier_scaled_upper=float(cross_hi),radial_shifted_minimum_coefficients=radial,direct_temporal_logdrive_lower=float(logdrive),direct_eta_shift_upper=float(eta_dot),direct_growth_coefficient_lower=float(direct_growth),scope='conditional actual radial layer weak identities, first correction sign under smooth reference, local finite band inverses only; no full receiver sign or high-frequency tail')

if __name__=='__main__':print(json.dumps(run(),indent=2))
