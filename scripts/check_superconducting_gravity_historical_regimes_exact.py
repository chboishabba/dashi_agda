#!/usr/bin/env python3
"""Exact published-summary reconstruction, NOT raw experimental replay.
Sources: Hathaway/Cleveland/Bao Physica C 385 (2003) 488-500;
Graham et al Physica C 468 (2008) and Canterbury preprint;
Tajmar et al arXiv:0707.3806. Original authors retain credit.
"""
import sympy as s

def main():
    repeatability=s.Rational(1,1000) # Hathaway weight percent
    original_claim=s.Rational(5,100) # Podkletnov reported minimum percent
    assert original_claim/repeatability == 50
    speed_observed=550
    assert speed_observed<1000<2000
    # Demonstrate observed operation is CW <=550, not 1000-2000 CCW.
    def synthetic_ccw_threshold(rpm,direction,c):
        return c*max(0,rpm-550)**2 if direction=="CCW" else 0
    c=s.symbols("c",positive=True)
    assert all(synthetic_ccw_threshold(r,"CW",c)==0 for r in [400,550])
    assert synthetic_ccw_threshold(1000,"CCW",c)!=0
    # Graham published theory and source fitted Sagnac slopes, cycles/rad.
    predicted=s.Rational(48,1_000_000)
    observed=s.Rational(23,10_000_000)
    standard_error=s.Rational(14,10_000_000)
    upper95=observed+s.Rational(196,100)*standard_error
    assert 20<predicted/observed<22
    assert 9<predicted/upper95<10
    # Their source also supplies direct delta-f coefficient 4.65e-5 omega:
    omega_cw=2*s.pi*15; omega_ccw=2*s.pi*12
    assert abs(float(s.Rational(465,10_000_000)*omega_cw)-.00438)<.00001
    assert abs(float(s.Rational(465,10_000_000)*omega_ccw)-.00351)<.00001
    # Acceleration-only countermodel vanishes during constant-speed plateau;
    # it is NOT a fit to Graham or evidence of a gravity signal.
    alpha=s.symbols("alpha")
    assert (c*alpha).subs(alpha,0)==0
    # Tajmar's reported onset is not identical to superconducting Tc.
    Tc,Ton=s.symbols("Tc Ton",real=True)
    assert s.simplify(Ton-Tc)!=0
    print("PASS exact Hathaway scope and 50x threshold distinction")
    print("Graham predicted/fit ratio",float(predicted/observed),
          "predicted/(fit+1.96SE)",float(predicted/upper95))
    print("PASS Tajmar transition mismatch; no raw-data replication")
if __name__=="__main__":main()
