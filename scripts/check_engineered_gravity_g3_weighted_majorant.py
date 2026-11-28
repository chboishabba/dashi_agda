"""Weighted original G3 centre-patch analytic majorant, not numerical evolution."""
from fractions import Fraction as F
import sympy as s


def main():
    # Same nested complex radii and original KK initial bounds as split donor.
    rho=F(1,16); n=80; eta_h=F(1,128); eta_K=F(32); eta_P=F(1)
    I=11; P=25; dP0=384; K=eta_K
    assert F(8)/(1-8*4*eta_h)<I
    # Inverse row norm for Gamma; derivative inverse row norm <= I^2*4P.
    G=F(3,2)*I*P; dI=4*I*I*P
    dG=F(3,2)*(dI*P+I*dP0)
    Ric=8*dG+32*G*G
    # K products: tr(h^-1 K) <=4 I K, and each Kh^-1 K entry <=4 I K^2.
    # Conservative 48 I K^2 retained from prior donor.
    sources=[2*K/eta_h,(Ric+48*I*K*K)/eta_K,F(0)]
    # Principal component caps on scaled system; K_t depends on dP only.
    principal=[F(0),8*F(3,2)*I*eta_P/eta_K,2*eta_K/eta_P]
    cF=max(sources); cA=max(principal)
    assert cF<400000 and cA==64
    # V components are scaled by their own radii, now unit polydisc.
    # Scalar comparison retains block scaling in coefficients.
    A=n*(3*cA/(rho*cF)+1); T=F(3,32)/(A*cF); W=1/(4*A)
    assert W<1 and F(1,2)*W-A*W*W/2==cF*T
    old=F(3,3276824576000)
    assert T>old
    # Exact implicit PDE for the weighted component comparison.
    z,w,t=s.symbols('z w t'); P0=(1-z/rho)*w-A*w*w/2-cF*t
    wt=-s.diff(P0,t)/s.diff(P0,w); wz=-s.diff(P0,z)/s.diff(P0,w)
    assert s.simplify(wt*(1-z/rho-n*w)-cF-3*n*cA*wz)==0
    # Compatibility of first-order derivative variable: P_t = d h_t.
    # Written proof: d_t(P_i-d_i h)=0, zero initial data imply zero.
    # Cauchy tails for exact even metric on half time disk, interior spatial patch.
    metric=eta_h*W; tail=metric/48
    # |x_i|<=rho/12 leaves a polydisc derivative radius rho/12 inside sum <=rho/2.
    spatial=12*tail/rho
    # temporal derivative of even tail at t=T/2: sum_{j>=3} 2j (1/2)^(2j-1)=5/18.
    j=s.symbols('j',integer=True,nonnegative=True)
    fac=s.summation(2*j*s.Rational(1,2)**(2*j-1),(j,3,s.oo))
    assert fac==s.Rational(5,18)
    temporal=metric*F(5,18)/T
    # Stronger cross-block tail: h_t=-2K and K is odd.
    # At half radius K tail after cubic <= eta_K W/24. Integrate
    # each term to bound the metric tail, retaining T and 1/6.
    cross_temporal=eta_K*W/12
    cross_metric=eta_K*W*T/144
    cross_spatial=12*cross_metric/rho
    assert cross_metric<tail and cross_temporal<temporal
    print('cross-block tails',float(cross_metric),float(cross_spatial),float(cross_temporal))
    print('block scales',eta_h,eta_K,eta_P,'source caps',sources,'principal caps',principal)
    print('T',T,float(T),'improvement',float(T/old),'W',W)
    print('quartic exact-coefficient tails at T/2',float(tail),float(spatial),float(temporal))
    print('PASS weighted coefficient and conditional Cauchy receiver envelope')


if __name__=='__main__':main()
