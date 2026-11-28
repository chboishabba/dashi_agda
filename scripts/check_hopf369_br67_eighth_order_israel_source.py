#!/usr/bin/env python3
"""BR67 eighth-order FULL moving nonlinear Israel source correction.

BR66 exact source correction is
   T_ab(t)=2 [bpp_+(t)-bpp_-(t)-2m(t)j(t)] phi(t) eta_ab.
The original BR47/52 physical source uses DIVIDED Taylor coefficients.
Therefore T_n=2 eta_ab {[(bpp+-bpp-)phi]_n
                           -2[(m*j)*phi]_n}.
This is a nontrivial *three-factor* convolution, not a pairwise
linearization freezing m or j. All 10 Israel components, original D/E
allocations and the full 15 metric/5 gauge source are retained by the
BR34 rows; this checker pays the missing geometric normal/shape term
through orders 0..8 and rejects the naive frozen-mean approximation.

Independently constructed direct two-face K and actual reference BR34
Israel source are compared at every order using the true original
metric_rows source implementation. The source is a concrete polynomial
family, not a proof of weighted PDE estimates or evolving Einstein
solutions.
"""
import argparse
from fractions import Fraction as F
import sympy as s
from check_hopf369_br52_all_order_material_flux import (
    ORDER,trim,var,add,sub,mul,scale
)
from check_hopf369_br_warped_physical_attachment import (
    metric_rows,metric_side,E4,keys,trace4,dec
)

def pol(jet,t):
    return sum(s.Rational(*v.as_integer_ratio())*t**i
               for i,v in enumerate(jet))

def sp_jet(offset):
    return trim([F(offset+2*k+1,11+offset+3*k) for k in range(ORDER+1)])

def independent():
    bdiff=sp_jet(1)
    mean=sp_jet(2)
    jump=sp_jet(3)
    phi=sp_jet(4)
    corrected=scale(2,mul(sub(bdiff,scale(2,mul(mean,jump))),phi))
    t=s.Symbol("time")
    direct=s.expand(2*(pol(bdiff,t)-2*pol(mean,t)*pol(jump,t))*pol(phi,t))
    for n in range(ORDER+1):
        assert s.expand(direct).coeff(t,n)==s.Rational(*corrected[n].as_integer_ratio())
    # Independent negative controls: the time derivatives of the
    # physical mean, tension jump and graph displacement cannot vanish
    # by replacing them with only their values at time zero.
    frozen=s.expand(2*(pol(bdiff,t)-2*mean[0]*jump[0])*phi[0])
    assert s.expand(direct-frozen)!=0
    assert corrected[8]!=0
    return corrected

def check():
    t=s.Symbol("time")
    mean=sp_jet(2);j=sp_jet(3);phi=sp_jet(4);diff=sp_jet(1)
    mm,jj,ff,bd=map(lambda x:pol(x,t),(mean,j,phi,diff))
    kp=mm+jj/2;km=mm-jj/2
    Hp=s.Matrix(4,4,lambda a,b:
        (s.Rational((min(a,b)+2)*(max(a,b)+3)%17-8,13)
         + t*s.Rational(a+b+2,17)
         +t*t*s.Rational(a+b+3,19)) )
    Hp=(Hp+Hp.T)/2
    Hm=Hp+2*jj*ff*E4
    bp=s.Matrix([1+t*s.Rational(i+2,7) for i in range(4)])
    bm=s.Matrix([s.Rational(i-1,11)+t*t*s.Rational(i+1,13) for i in range(4)])
    lp=s.Rational(2,7)+t*s.Rational(1,17)
    lm=s.Rational(-3,11)+t*s.Rational(2,19)
    z=s.Matrix([s.Rational(i-2,17)+t*s.Rational(i+1,23) for i in range(4)])
    xp=s.Matrix(4,4,lambda a,b:s.Rational(a+b+1,17)+t*s.Rational(a+b+3,29))
    xm=s.Matrix(4,4,lambda a,b:s.Rational(a+b-2,19)+t*s.Rational(a+b+4,31))
    def tensor(H,b,l):return H.row_join(b).col_join(b.T.row_join(s.Matrix([[2*l]])))
    pp=tensor(Hp,bp,lp);pm=tensor(Hm,bm,lm)
    ppx=tensor(xp,s.zeros(4,1),0);pmx=tensor(xm,s.zeros(4,1),0)
    Kp=metric_side(pp,ppx,z,jj/2)[2]
    Km=metric_side(pm,pmx,z,-jj/2)[2]
    # Actual physical general-mean curvature is reference plus m H,
    # and the separately retained moving second-warp shape source.
    fullRp=Kp+mm*Hp+(kp**2+bd)*ff*E4
    fullRm=Km+mm*Hm+km**2*ff*E4
    induced=Hp+2*kp*ff*E4
    assert (induced-Hm-2*km*ff*E4).applyfunc(s.expand)==s.zeros(4)
    R=2*(fullRp-fullRm)-2*jj*induced
    sourceCorrection=2*(bd-2*mm*jj)*ff*E4
    source_taylor=independent()
    for allocation in "DE":
        actual=metric_rows(pp,ppx,pm,pmx,z,jj,allocation)
        # Original 10 Israel rows are at offsets 14..23.
        J=s.Matrix(4,4,lambda a,b:
          actual[14+keys.index((min(a,b),max(a,b)))])
        assert (R-J-sourceCorrection).applyfunc(s.expand)==s.zeros(4)
        for a,b in keys:
            v=s.expand(R[a,b]-J[a,b])
            for order in range(ORDER+1):
                expected=E4[a,b]*s.Rational(
                    *source_taylor[order].as_integer_ratio())
                assert v.coeff(t,order)==expected,(allocation,a,b,order)
    print("PASS BR67 all 9 time orders, 10 Israel entries, original BR34 D/E")
    print("PASS general-mean/nonzero tension/warp source triple Leibniz and negative controls")

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--part",choices=["coeff","physical"],default="coeff")
    a=p.parse_args()
    if a.part=="coeff":
        independent()
        print("PASS BR67 all-order triple product coefficients, nonzero high-jet control")
    else:
        check()

if __name__=="__main__":main()
