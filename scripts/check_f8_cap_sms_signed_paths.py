"""Conditional original F8 SMS finite-path sign by common receiver-clock shift.
Reuse smooth radial layer, original cap, signed source jets through order 17,
and original M=5 tilted Fourier complement. No native kernel or physics claim.
"""
from fractions import Fraction as Q
import json
import sympy as S


def run():
    nchecks=0
    def check(x):
        nonlocal nchecks
        assert x
        nchecks+=1
    b, tau, dz, v, acc, D, c, xi = S.symbols('b tau dz v acc D c xi', real=True)
    beta=S.sqrt(1+b*b);dt=lambda f:S.diff(f,b)*(-b/beta)
    a=b/(1+b*b)**2
    check(S.simplify(dt(-b/beta)-a)==0)
    check(S.simplify(beta*dt(beta)+b*b/beta)==0)
    check(S.simplify(dt(a)/a-(3*b*b-1)/(1+b*b)**S.Rational(3,2))==0)
    check(S.simplify(dt(dt(a))/a-(12*b**4-15*b*b+1)/(1+b*b)**3)==0)
    q=tau*tau-dz*dz;L=tau-v*dz
    deriv=lambda f:S.diff(f,tau)+v*S.diff(f,dz)+v*S.diff(f,b)+acc*S.diff(f,v)
    check(S.expand(L*L-(1-v*v)*q-(dz-v*tau)**2)==0)
    check(S.expand(deriv(q)-2*L)==0)
    check(S.expand(deriv(deriv(q))-2*(1-v*v-dz*acc))==0)
    eta=q*(1-c*c)/(4*b*xi)
    check(S.cancel(deriv(eta)-(1-c*c)/(4*b*xi)*(2*L-q*v/b))==0)
    check(S.cancel(deriv(deriv(eta))-(1-c*c)/(4*b*xi)*(2*(1-v*v-dz*acc)-4*L*v/b+q*(2*v*v/(b*b)-acc/b)))==0)
    # Original support-clock excess: sum(D_leg-displacement_leg)<rho.
    # Hence the long leg has c=-cos(theta)>=1-rho/D; no sign claim
    # is needed for individual short-leg cosines. R lags sum <= .01.
    rho=Q('.000361');h=Q('.01');br=Q('.087');be=Q('.997');bhi=Q('.09')
    dmin=Q('2.4763');lmax=Q('2.66');cmin=1-rho/dmin
    check(cmin>Q('.9998'))
    # Long leg: dz<-.907; |v_target|<.09, D<2.66. Target-only shift.
    nd=be-bhi-bhi*lmax;check(nd>0)
    dp2=1-bhi*bhi+nd*nd/(lmax*lmax)
    check(dp2>Q('1.027')**2)
    # Self R leg: both endpoints shifted, |dz|<=.09*tau, |v_t-v_s|<=.09*tau,
    # |a_t-a_s|<=.18*tau, D>=.99*tau.
    check(1-bhi*bhi>Q('.99')**2)
    check((1+3*bhi*bhi)<2 and 1+15*bhi*bhi+12*bhi**4<4)
    check(2*bhi*bhi<Q('.0163'))
    check(2*(bhi*bhi+bhi*Q('.18'))<Q('.05'))
    check(bhi*bhi/Q('.99')<Q('.009'))
    check(Q('.05')/(2*Q('.99'))+Q('.009')**2/Q('.99')<1)
    plo,phi=Q('1.025'),Q('1.08')
    check(cmin*Q('1.027')-Q('.009')*h>plo)
    check(lmax/dmin+Q('.009')*h<phi)
    check((1+bhi+phi*phi)/dmin<1)
    check(1+h<2) # |p'|<2 along any selected path
    # Green analytic factor bounds from original positive coefficient tail.
    e=Q(1,16);Alo=Q(17,32);Ap=Q(15,2);App=Q(11);Appp=Q(35)
    check(2*Q(35,8)/(1-e)**3<App)
    check(6*Q(35,8)/(1-e)**4<Appp)
    Bp=Q('4.5');Bpp=Q(8);S0=Q(15,4);S1=App;S2=Appp
    check(Ap/2+e*App<Bp and App/2+e*Appp<Bpp)
    # B0=3A/2-eta A'; S1 series coefficients (n-1/2)a_n.
    # |S1'|<=A'', |S1''|<=A''' since n>=2 tail is positive.
    # Short-leg eta derivatives: both inverse endpoint b factors have
    # first relative bound 1, second bound 3; their product 2 and 8.
    f=h*h/(4*br*br);ep=Q('.02');epp=Q('.1')
    check(f*(Q('.0163')+2)<ep)
    check(f*(Q('.05')+4*Q('.0163')+8)<epp)
    # N=integral (tau-u) a(s+u) du, |N'|<=2N, |N''|<=4N.
    # B=(B0+N*S1/(2*z))/xi. Bound normalized B and its jets.
    n=bhi*h*h/2
    Bbar=Q(5,4)-n*S0/(2*br)
    Bbar1=Bp*ep+n/(2*br)*(3*S0+S1*ep)
    Bbar2=Bpp*ep*ep+Bp*epp+n/(2*br)*(11*S0+6*S1*ep+S2*ep*ep+S1*epp)
    check(Bbar>1)
    check(1+Bbar1/Bbar<2)
    check(3+2*Bbar1/Bbar+Bbar2/Bbar<5)
    # Every R self factor is N*sin²(theta) or B; log-jet bounds 2,5.
    # Product of <=5 self factors, times final b_R^(3/2).
    P1=5*2+Q(3,2);P2=5*5+5*4*4+2*10*Q(3,2)+Q(9,4)
    check(P1<12 and P2<150)
    # Long-leg eta: one moving endpoint only; angle cap much tighter.
    f=(1-cmin*cmin)/(4*br*be);ep=Q('.03');epp=Q('.1')
    check(f*(Q('5.32')+lmax*lmax)<ep)
    check(f*(Q('2.18')+2*Q('5.32')+3*lmax*lmax)<epp)
    # Direct free angular factor A: relative jets <=1,2.
    check(Ap*ep/Alo<1)
    check((App*ep*ep+Ap*epp)/Alo<2)
    # Cross after one angular IBP: C=N*c/D >0, adverse B.
    # N=dz-v_source*tau; source clock fixed, |v_source|>.7.
    Nlo=Q('.848');check(Q('.7')*Q('2.64')-1==Nlo)
    check(Q('2.6492')-Q('.0037')>Q('2.64'))
    check(Q('.8')<Nlo and bhi<Nlo)
    # |C'|/C<=2 and |C''|/C<=3 via N'/N,N''/N<=1.
    d1=Q('.44');d2=Q('.41');check(phi/dmin<d1 and 1/dmin<d2)
    check(1+d1<2 and 1+2*d1+2*d1*d1+d2<3)
    # B, B', B'' relative to C (not relative to possibly signed B).
    f=lmax/(cmin*be)
    B0C=f*(Q(3,2)/Nlo+S0/(2*br))
    B1C=f*(Bp*ep/Nlo+(2*S0+S1*ep)/(2*br))
    B2C=f*((Bpp*ep*ep+Bp*epp)/Nlo+(6*S0+4*S1*ep+S2*ep*ep+S1*epp)/(2*br))
    check(B0C<100 and B1C<250 and B2C<1000)
    # Let a=P*C and d=P*B; direct case a=P*A, d=0.
    a1=Q(14);a2=Q(201);d0=Q(100);d1=Q(1450);d2=Q(22000)
    check(12+2<=a1 and 150+2*12*2+3<=a2)
    check(12*100+250<=d1 and 150*100+2*12*250+1000<=d2)
    # Signed source jet H_j: H_j'=p H_(j+1) after clock shift.
    a,ap,app,p,pp,H0,H1,H2=S.symbols('a ap app p pp H0 H1 H2')
    dd=lambda f:S.diff(f,a)*ap+S.diff(f,ap)*app+S.diff(f,p)*pp+S.diff(f,H0)*p*H1+S.diff(f,H1)*p*H2
    check(S.expand(dd(dd(a*H0))-(app*H0+(2*ap*p+a*pp)*H1+a*p*p*H2))==0)
    # Each selected SMS integrand has positive main bracket and a smaller
    # adverse cross bracket, using H_(j+1)>=10000 H_j.
    slope=Q(10000);B=Q('1.01');check(1+bhi*bhi<B)
    check(2*Q('1.005')+bhi*bhi<3)
    main=plo*plo-1-(B*(2*a1*phi+2)+3*phi)/slope-(B*a2+3*a1)/slope**2
    adverse=d0*(B*phi*phi+1)/slope+(B*(2*d1*phi+2*d0)+3*d0*phi)/slope**2+(B*d2+3*d1)/slope**3
    check(main>Q('.047'));check(adverse<Q('.022'));check(main-adverse>Q('.025'))
    # Direct family comparison with E4, all positive source components.
    e4=B*phi*phi+1+(B*(2*a1*phi+2)+phi)/slope+(B*a2+a1)/slope**2
    check(e4<3 and 2*main/e4>Q('.04'))
    # D source order<=4; each self leg +2, cross +1, SMS/E4 +2.
    check(4+2*5+1+2==17)
    check(6+sum(6-i for i in range(6))==27)
    # SMS coefficients dominated by 4 times the EXISTING E4 majorants.
    b=bhi;betahi=Q('1.005');check(1+b*b<betahi**2)
    check(b*b*(1+b*b)/2<4*Q('.003'))
    check((4*b*b+7*b**4+2*b*b*(1+b*b))/2<4*Q('.009'))
    check(((4*b*b+14*b**4+9*b**6)+4*b*b+2*b**4)/2<4*Q('.009'))
    check(b*b/2<4*Q('.003'))
    direct=Q('4.536e-270')*Q('.04');tail=4*Q('7.102e-279')
    check(direct-tail>Q('1.814e-271'))
    return dict(checks=nchecks,scope='conditional original 27-term SMS sign and inherited full-frequency complement; analytic path-domain/shift attachment and prior bounds required',long_angle_lower=float(cmin),transport_speed=[str(plo),str(phi)],main_bracket_lower=str(main),adverse_bracket_upper=str(adverse),cross_margin_lower=str(main-adverse),direct_sms_to_e4_lower=str(2*main/e4),selected_terms=27,source_max_derivative=17,direct_magnitude_lower='1.8144e-271',complement_upper='2.8408e-278',strict_full_sms_upper='-1.814e-271')

if __name__=='__main__':
    print(json.dumps(run(),indent=2))
