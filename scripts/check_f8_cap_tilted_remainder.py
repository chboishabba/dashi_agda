"""Full-frequency tilted E4 remainder bound for original finite signed path cut.
Conditional on inherited smooth causal radial layer; exact rational budgets.
"""
from fractions import Fraction as Q
from math import factorial,floor
import json
from check_f8_cap_all_frequency import root

K=Q(1780000);eps=Q('.04');rho=Q('.000361');mcut=5
E=Q('2.71828');scale=10**300
# Positive rational Taylor lower for e. Upper bounds use rounded-down exponent.
assert sum((Q(1,factorial(j)) for j in range(11)),Q(0))>E>Q('2.7')
def expneg(x):
    assert x>0
    return E**(-floor(x))

def laplace(a,b):
    # Integral_0^infty exp(-a/t-b*t) <= width*exp(-2sqrt(ab)).
    # For t<=2t0: (t-t0)^2/t >= (t-t0)^2/(2t0).
    # For t>=2t0: (t-t0)^2/t >= t/4. Drop the extra tail exponential.
    t0=root(a/b)[1]
    return root(2*Q(22,7)*t0/b)[1]+4/b,2*root(a*b)[0]

def selfrho(m,b,a,d,g):
    # e^-x I0(x), e^-x I1(x)/x decrease by angular integral.
    # Exact Laplace angular moments 1/sqrt(g(g+2d)), 1/[g(g+2d)]^(3/2).
    v=g*(g+2*d);w=root(v)[0]
    return Q(3,2)/(b*K*w)+a*(1+m*m)/(2*K*v*w)

def run():
    # Original full compact temporal drive support, b>=.95 via prior clock.
    from check_f8_global_wall_kernel import Fbox
    f=Fbox(Q(1));assert Fbox(Q('.95'))[0]>f[1]+Q('.065')
    assert 64*Q('.95')**5>36 # source conjugated amplitude <=8
    # Receiver weights E4, b<.09 on R; norm>=1/15 from original owner.
    b=Q('.09');assert b**3<=Q('.027')**2
    assert b*b*(1+b*b)/4<Q('.003')
    assert (4*b*b+7*b**4)/4<Q('.009')
    assert (4*b*b+14*b**4+9*b**6)/4<Q('.009')
    # Original D Fourier polynomial, r*>2.5, |k|>=K.
    rr=Q('2.5');assert sum(Q(c)/rr**(5-j)/K**(4-j) for j,c in enumerate([3,3,3,2,1]))<Q('.5')
    # Free comparison K+ = I0(sqrt(K²+Vmax)*D)/2.
    # Hdiff>=D, exp((sqrt(K²+Vmax)-K)*D)<2.
    V=Q(2535,4);assert V/(2*K)*Q('2.66')<Q(1,2)
    assert V<2*K+1 and K*Q('2.3')>2000**2
    assert (Q('2.6492')-Q('.065'))**2-1>Q('2.3')**2
    assert (Q('2.6492')-Q('.0037'))**2-1>Q('2.4')**2
    # I0(x)<=e^x/sqrt(x), I1<=I0. Cross |2(Kxi-v Kt+3K/2b)|<=4000(1+m²).
    assert 4*(K+1)*Q('5.32')/(4*Q('2.4'))/1000+3*Q(1,2000)/Q('.997')<4000
    assert 4000*Q('.0037')<15
    # Laplace source and receiver factors. Factor e^(K H(0)) and e^(K eps) separately.
    wr,er=laplace(eps/2,K);ws,es=laplace(Q('.065')/4,Q('.8')*K)
    wq,eq=laplace(Q('.05')*Q('.99'),Q('1.03')*K)
    radA=eps**5*wr;radB=8*eps**6;source=8*ws
    # X^j exp(-.01 X) <= (j/(.01 e))^j; use e>2.7.
    P=[Q(1)]+[(Q(j)/Q('.027'))**j for j in range(1,5)]
    obsP=15*Q('.027')*wq*(Q('.3')*(2*P[2]+8*P[3]+4*P[4])+Q('.18')*P[2]+Q('.009'))
    obs0=15*Q('.027')*wq*Q('.003')
    # Total e^3 upper allowance for raw bump normalization, even contour branch.
    base=es+eq-K*rho-3;assert base>0
    def ceilgrid(x):return (x.numerator*scale+x.denominator-1)//x.denominator
    # Integrate symmetric low real-frequency bands using 1/pi<1/3.
    edges=list(map(Q,['0','.5','1','1.5','2','2.5','3','4','5','6','7','8']))
    rows=[];low=0
    for a,m in zip(edges,edges[1:]):
        e=selfrho(m,Q('.997'),Q('.26'),Q('.7'),Q('.09'))
        r=selfrho(m,Q('.087'),Q('.09'),Q('.99'),Q('.035'))
        assert max(e,r)<1
        d=r**6/(1-r)
        c=sum(e**i*r**(6-i) for i in range(6))/(1-r)+e**6/((1-r)*(1-e))
        residual=Q('.001')*d+2*15*(1+m*m)*c
        k2=K*K*(1+m*m);obs=(obsP*k2**2+obs0*k2**3)/2
        radial=min(radA*expneg(base+er),radB*expneg(base+root(eps*K*a)[0]))
        bound=K*(m-a)/3*source*radial*obs*residual
        units=ceilgrid(bound);low+=units
        rows.append(dict(real_frequency_over_K=[str(a),str(m)],rho_E=float(e),rho_R=float(r),direct_remainder_multiplier=float(d),cross_remainder_multiplier=float(c),bound_display=float(Q(units,scale))))
    # High real-frequency complement: all-frequency complex Bessel bound, after tilt.
    # |V_i| <= h B+(4/3) a h^(3/2) sqrt(|k|) <=2 sqrt(omega), omega>=K.
    for h,b,a in ((Q('.0037'),Q('.997'),Q('.26')),(Q('.01'),Q('.087'),Q('.09'))):
        assert h*(Q(3,2)/b+Q(8,3)*a)<2
    C=Q(3617,250000);B=Q(102919,144565);loss=4*C**3/(27*Q('.01')**2)
    assert 122**3>K and B+C*122+loss<3
    # Two inverse product <=4 exp(3+.01 sqrt(omega))<108 exp(.01 sqrt(omega)).
    # C_RE<=30 omega²/K². 6 mixed terms + E tail; f_R<=.001 Hs, f_E<=2 Hs.
    # |F_R-P| <=108*64*421 omega^5/K² exp(.01 sqrt(omega))*Hs.
    # Original contour bound exp(-.2 sqrt(omega)) remains .19 after inverse growth.
    # |D| and |Drr| readout <=(2 obsP+4 obs0) omega^6; integrate omega^11 exactly.
    w0=floor(root(8*K)[0]);a=Q('.19');assert w0*w0<=8*K
    poly=2*sum(Q(factorial(23),factorial(j))*Q(w0)**j/a**(24-j) for j in range(24))
    tail=source*radB*(2*obsP+4*obs0)*Q(108*64*421,3)/K**2*poly*expneg(base+a*w0)
    tail_units=ceilgrid(tail);total=Q(low+tail_units,scale)
    assert total<Q(1,10**270)
    return dict(scope='conditional original E4 full-frequency higher-wall remainder after 27 signed terms; inherited smooth causal layer and Fourier contour attachment',tilt=str(K),low_band_rows=rows,low_upper_display=float(Q(low,scale)),tail_upper_display=float(Q(tail_units,scale)),total_upper_display=float(total),exact_upper_numerator=str(low+tail_units),exact_upper_denominator='1e300',strict_upper='1e-270',source_width=float(ws),radial_width=float(wr),receiver_width=float(wq),source_exponent_lower=float(es),radial_exponent_lower=float(er),receiver_exponent_lower=float(eq),receiver_p_prefactor=float(obsP),receiver_a0_prefactor=float(obs0),tail_start_sqrt=w0,source_clock_guard=True)
if __name__=='__main__':print(json.dumps(run(),indent=2))
