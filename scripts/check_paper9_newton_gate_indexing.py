#!/usr/bin/env python3
"""Local exact Newton-indexing regression and Agda source-contract audit.

This is a structural and algebraic test, NOT a proof of Hecke41 coefficients,
analytic rigidity, or Agda typechecking. All arithmetic is exact.
"""
from fractions import Fraction
from pathlib import Path
from random import Random

ROOT = Path(__file__).resolve().parents[1]
PRODUCER = ROOT / "DASHI/Moonshine/CM163Hecke41FullIntegerMatrixExact.agda"
DIVIDER = ROOT / "DASHI/Moonshine/CM163BishopHecke41IntegerPrefixCertificateExact.agda"

def audit_sources():
    m = PRODUCER.read_text()
    d = DIVIDER.read_text()
    assert "nextE j es k = build (λ _ n → divPositive (newton j es (suc k) n) k) 41" in m
    assert "divPositive (+ n) d = + (n / suc d)" in d
    assert "divPositive -[1+ n ] d = Z.- (+ (suc n / suc d))" in d
    for name in ("originalNewtonCheck", "originalColumnCheck", "originalSymmetryCheck", "originalPacketCheck"):
        assert name + " : Dec" in m
    assert "(newton j es (suc k) n) (suc k)" not in m

def elementary_from_power_sums(p, degree):
    es = [Fraction(1)]
    for k in range(degree):
        numer = sum((-1)**i * es[k-i] * p[i+1] for i in range(k+1))
        es.append(numer / (k+1))
    return es

def bad_elementary_from_power_sums(p, degree):
    es = [Fraction(1)]
    for k in range(degree):
        numer = sum((-1)**i * es[k-i] * p[i+1] for i in range(k+1))
        es.append(numer / (k+2))  # Incorrect extra successor.
    return es

def elementary_from_roots(roots):
    es = [Fraction(1)]
    for root in roots:
        es = [es[0]] + [es[i] + root * es[i-1] for i in range(1,len(es))] + [root*es[-1]]
    return es

def run():
    audit_sources()
    rng = Random(410163)
    tested = 0
    for degree in (1, 2, 3, 5, 7, 41):
        for roots in ([0]*degree, list(range(1,degree+1)),
                      [rng.randrange(-30,31) for _ in range(degree)]):
            p = [0] + [sum(r**k for r in roots) for k in range(1,degree+1)]
            actual = elementary_from_power_sums(p, degree)
            expect = elementary_from_roots(roots)
            assert actual == expect, (degree, roots)
            tested += 1
    p = [0, Fraction(7)]
    assert elementary_from_power_sums(p,1)[1] == 7
    assert bad_elementary_from_power_sums(p,1)[1] != 7
    tested += 1
    print(f"PAPER9_NEWTON_SOURCE_CONTRACT_OK cases={tested} degrees=1,2,3,5,7,41")
    print("SCOPE: source shape and elementary Newton algebra; no kernel/analytic claim")

if __name__ == "__main__":
    run()
