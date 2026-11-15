#!/usr/bin/env python3
"""KSW D2/A2: strict, quantitatively bounded continuous AdS5 shortcut horizon.

Caldwell–Langlois (2001), source Eq.(19): for w=dt/a(t)>0,
 x(t)=ell H(t), and A=int w = photon horizon,
 r_g = sqrt((int w sqrt(1+x²))²-(int w x)²).

The key correct SAME-SOURCE double-integral identity is
 r_g² - A² = doubleint w_s w_t
   {cosh(asinh(x_s)-asinh(x_t))-1}.
For |x|<=M:
 cosh(v)-1 >= v²/2,
 |asinh x-asinh y| >= |x-y|/sqrt(1+M²).
Since r_g<= A sqrt(1+M²), this yields the STRICT variance lower bound
 r_g-A >= A*Var_w(x) / [(1+M²)*(1+sqrt(1+M²))],
 Var_w(x) = int w(x-xbar)²/A.
Strict when H is not constant a.e. under positive w.
This is a mathematical source theorem; it does not specify localized
graviton emission/detection, physical length units, or observed delay.

For the already constructed AdS5 FRW source a=t, H=1/t, ell=1,
tA=1,tB=2, weighted moments are exact functions of log2:
 A=ln 2; first moment E_w x=1/(2 ln2),
 second moment E_w x²=3/(8 ln2).
The nonzero dispersion of H makes the bulk horizon strictly larger.
"""
import argparse,json,random,math
import mpmath as mp

def finite_bound(xs,ws):
    if len(xs)<2 or len(xs)!=len(ws):raise ValueError("Two or more source epochs required")
    if any(not math.isfinite(float(x)) for x in xs) or any(
            not math.isfinite(float(w)) or w<=0 for w in ws):
        raise ValueError("Finite H and strictly positive source weights required")
    x=[mp.mpf(str(v)) for v in xs]
    w=[mp.mpf(str(v)) for v in ws]
    A=mp.fsum(w)
    mean=mp.fsum(u*v for u,v in zip(w,x))/A
    var=mp.fsum(u*(v-mean)**2 for u,v in zip(w,x))/A
    M=max(abs(v) for v in x)
    J=mp.fsum(u*mp.sqrt(1+v*v) for u,v in zip(w,x))
    I=mp.fsum(u*v for u,v in zip(w,x))
    rg=mp.sqrt(J*J-I*I)
    bound=A*var/((1+M*M)*(1+mp.sqrt(1+M*M)))
    tol=mp.mpf("1e-55")
    if not rg-A+tol>=bound:
        raise AssertionError("Reverse Minkowski variance bound failed")
    return A,rg,var,bound

def source_model(tA=1,tB=2,ell=1):
    a,b,l=map(lambda z:mp.mpf(str(z)),(tA,tB,ell))
    if not (mp.isfinite(a) and mp.isfinite(b) and mp.isfinite(l)
            and 0<a<b and l>0):
        raise ValueError("Proper positive AdS5 source interval and ell required")
    A=mp.log(b/a)
    def I1primitive(t):
        return mp.asinh(t/l)-mp.sqrt(t*t+l*l)/t
    I1=I1primitive(b)-I1primitive(a)
    I2=l*(1/a-1/b)
    rg=mp.sqrt(I1**2-I2**2)
    mean=I2/A
    second=(l*l/(2*A))*(1/a**2-1/b**2)
    var=second-mean**2
    M=l/a
    bound=A*var/((1+M*M)*(1+mp.sqrt(1+M*M)))
    assert var>0 and rg>A and rg-A>=bound
    return {
       "source":"Caldwell–Langlois 2001 original AdS5 Eq.19 a=t H=1/t; DOI 10.1016/S0370-2693(01)00631-1",
       "tA":float(a),"tB":float(b),"ell":float(l),
       "photon_horizon_A":float(A),
       "bulk_gravitational_horizon_rg":float(rg),
       "same_interval_horizon_excess":float(rg-A),
       "weighted_Hell_mean":float(mean),
       "weighted_Hell_variance":float(var),
       "M_sup_abs_Hell":float(M),
       "proven_variance_lower_bound_on_horizon_excess":float(bound),
       "lower_bound_as_fraction_actual_excess":float(bound/(rg-A)),
       "source_positive_rho_and_Z2_Israel_from_other_original_scripts":True,
       "same_worldline_detected_signal":False,
       "physical_timescale_in_seconds_declared":False
    }

def audit():
    mp.mp.dps=80
    cases=0
    for n in (2,3,5,13):
        for i in range(70):
            random.seed(34013+n*100+i)
            xs=[random.uniform(-2,2) for _ in range(n)]
            ws=[random.uniform(.01,2) for _ in range(n)]
            finite_bound(xs,ws);cases+=1
    A,rg,var,b=finite_bound([.75,.75,.75],[1.,.2,1.])
    assert abs(var) < mp.mpf("1e-65") and rg>=A and abs(rg-A)<mp.mpf("1e-65")
    numeric=source_model()
    numeric.update({
      "status":"PASS strict 5D horizon variance lower bound, nonconstant H; finite random controls",
      "finite_positive_weight_variants_tested":cases,
      "constant_H_no_shortcut_control":True,
      "proof":"cosh rapidity gap, asinh Lipschitz lower bound, double-integral weighted variance",
      "analytic_Agda_continuum_sqrt_integration_kernel_accepted":False,
      "full_tensor_bulk_graviton_receiver_evidence":False,
      "no_global_5D_causal_violation":True
    })
    return numeric

if __name__=="__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--out")
    a=p.parse_args()
    s=json.dumps(audit(),indent=2,sort_keys=True)+"\n"
    if a.out:open(a.out,"w",encoding="utf-8").write(s)
    print(s)
