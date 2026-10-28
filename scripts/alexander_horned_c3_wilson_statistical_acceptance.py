#!/usr/bin/env python3
"""Statistical acceptance bands for the actual horned-C3 noisy compiler.

Exact distribution-independent bounds conditional on the stated iid
trial protocol. Each trial's measured Wilson halftrace lies in [-1,1].
For N independent trials, Hoeffding yields
 Pr(|average - E average| >= epsilon) <= 2 exp(-N epsilon²/2).
These are conservative finite-sample guarantees, not lab calibration
or confidence bounds under correlated drift.
"""
import argparse
import json
import math


def ideal_gate_count(depth):
    if depth < 0:
        raise ValueError("depth must be nonnegative")
    return 3 * 4**depth


def expected_wilson(depth, sigma_degrees):
    if depth < 0 or sigma_degrees < 0 or not math.isfinite(sigma_degrees):
        raise ValueError("invalid depth or angle")
    return -math.exp(-ideal_gate_count(depth) * math.radians(sigma_degrees)**2 / 8)


def hoeffding_radius(trials, confidence=0.99):
    if trials < 1 or not 0 < confidence < 1:
        raise ValueError("invalid trial count or confidence")
    return math.sqrt(2 * math.log(2 / (1-confidence)) / trials)


def required_trials(absolute_error, confidence=0.99):
    if absolute_error <= 0 or not math.isfinite(absolute_error):
        raise ValueError("absolute_error must be positive and finite")
    if not 0 < confidence < 1:
        raise ValueError("invalid confidence")
    return math.ceil(2*math.log(2/(1-confidence))/absolute_error**2)


def familywise_radius(trials, tested_depths, confidence=0.99):
    if tested_depths < 1:
        raise ValueError("tested_depths must be positive")
    # Union bound, no independence needed BETWEEN depth measurements.
    return math.sqrt(2*math.log(2*tested_depths/(1-confidence))/trials)


def audit():
    assert [ideal_gate_count(i) for i in range(6)] == [3,12,48,192,768,3072]
    assert expected_wilson(0,0) == -1
    for depth in range(7):
        a=expected_wilson(depth,1.5)
        b=expected_wilson(depth+1,1.5)
        assert -1 <= a < b < 0
        assert math.isclose(math.log(-b),4*math.log(-a),rel_tol=1e-12,abs_tol=1e-12)
    assert hoeffding_radius(10000) < hoeffding_radius(1000)
    assert required_trials(.1) <= required_trials(.05)
    assert familywise_radius(10000,6) > hoeffding_radius(10000)
    return True


def main():
    p=argparse.ArgumentParser()
    p.add_argument("--noise-deg",type=float,default=1.5)
    p.add_argument("--depth",type=int,default=5)
    p.add_argument("--trials",type=int,default=500)
    p.add_argument("--confidence",type=float,default=.99)
    a=p.parse_args()
    audit()
    entries=[dict(depth=d,gates=ideal_gate_count(d),
                  expected_halftrace=expected_wilson(d,a.noise_deg))
             for d in range(a.depth+1)]
    print(json.dumps(dict(source="iid independent-axis Gaussian SU2 gate model",
          confidence=a.confidence,trials=a.trials,
          per_depth_radius=hoeffding_radius(a.trials,a.confidence),
          familywise_radius=familywise_radius(a.trials,len(entries),a.confidence),
          rows=entries),indent=2))


if __name__=="__main__":
    main()
