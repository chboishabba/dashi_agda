"""CDS sensitivity; public LSEG/Reuters/JPMorgan October 2026 observations.
Usage: python scripts/knowledge_capture_credit_stress_20261101.py
Not real-world default forecasts or an Agda kernel receipt.
"""
from math import exp

SPREAD_BPS = {"microsoft": 56, "amazon": 80, "oracle": 331,
              "coreweave_stress": 1100, "coreweave_peak": 1200,
              "lehman_comparator": 1400}
RECOVERY = (.2, .4, .6)

def risk_neutral_default(bps, recovery, years=5):
    return 1 - exp(-years * bps / 10000 / (1 - recovery))

def refi_increment(debt, fraction, repricing_bps):
    return debt * fraction * repricing_bps / 10000

def two_plus_default(p, common=0):
    assert 0 <= common <= p < 1
    residual = (p-common) / (1-common)
    return common + (1-common)*(3*residual**2*(1-residual)+residual**3)

def run():
    for name, bp in SPREAD_BPS.items():
        probabilities = [round(risk_neutral_default(bp, r)*100, 2)
                         for r in RECOVERY]
        print(name, bp, "5y risk-neutral PD % at R20/R40/R60", probabilities)
    assert abs(risk_neutral_default(1200, .4) - .6321205588) < 1e-8
    for fraction in (.17, .4, 1.):
        print("Refinancing share", fraction,
              [(shock, refi_increment(50e9, fraction, shock))
               for shock in (200, 400, 600)])
    assert refi_increment(50e9, .17, 400) == 340e6
    assert refi_increment(50e9, 1., 400) == 2e9
    p, q = .1, .08
    independent, joint = two_plus_default(p), two_plus_default(p, q)
    print("3-obligor assumed p=.1, common shock=.08: P(>=2)", independent, joint)
    assert abs(independent - .028) < 1e-12
    assert abs(joint - .08128544423440454) < 1e-12

if __name__ == "__main__":
    run()
