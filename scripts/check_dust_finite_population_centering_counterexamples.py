#!/usr/bin/env python3
"""Exact rational audit of Dust population-centering, Eq. (2).
Source: Dahal, Mandal, Gülbahar, Vegesna, Dust (2026), section 2.2.
Finite signed-probe cases are DASHI counterexamples, not source experiments.
"""
from fractions import Fraction as F
import json

def estimate(draws, sigma=F(1,7)):
    losses = [3*sigma*a+4 for a in draws]
    mean = sum(losses)/len(losses)
    centered = [mean-v for v in losses]
    return -sum(c*a for c,a in zip(centered, draws))/(len(draws)*sigma)

def main():
    cases = {
      "balanced_antithetic":[F(-1),F(1)],
      "uncentered_three":[F(0),F(1),F(2)],
      "constant_population":[F(1),F(1)],
      "unbalanced_four":[F(-1),F(0),F(1),F(3)]
    }
    got = {k:str(estimate(v)) for k,v in cases.items()}
    assert got == {
      "balanced_antithetic":"3",
      "uncentered_three":"2",
      "constant_population":"0",
      "unbalanced_four":"105/16"
    }
    print(json.dumps(got,indent=2))

if __name__=="__main__":
    main()
