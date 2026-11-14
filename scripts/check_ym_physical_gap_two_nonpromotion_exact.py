#!/usr/bin/env python3
"""Exact YM mass-gap nonpromotion tests for original D1/D2 proof obligations.

Model A: every cutoff has a strict lattice contraction q_n=1-1/n^2,
but a physical length-one separation spans n lattice steps, and
q_n^n >= 1-1/n -> 1. Hence NO common strictly positive physical
decay rate follows from q_n<1 at each n.

Model B: a finite positive Hamiltonian on a nonvacuum Hilbert space has
H_n = diag(1, 1/2, ..., 1/n). A *selected* e_1 test is uniformly
supported at energy 1 for every n, but the full non-vacuum spectral
infimum is 1/n -> 0. Selected-mode clustering is NOT a full gap.

The examples are exact rational witnesses, NOT original Wilson measure,
nor a YM mass-gap result. Numerical exp is not used.
"""
from fractions import Fraction
import argparse
import json

def verify(ns):
    rows = []
    for n in ns:
        if n < 2:
            raise ValueError("require n >= 2")
        a = Fraction(1,n)
        q = 1 - a*a
        correlation = q**n
        lower = 1 - a
        assert Fraction(0) < q < 1
        assert correlation >= lower
        assert correlation < 1
        chosen_e1_energy = Fraction(1)
        full_min_nonvacuum = Fraction(1,n)
        assert 0 < full_min_nonvacuum <= chosen_e1_energy
        rows.append({
            "cutoff_n":n,
            "lattice_spacing":[a.numerator,a.denominator],
            "q_n":[q.numerator,q.denominator],
            "physical_unit_correlation_lower":[lower.numerator,lower.denominator],
            "selected_probe_energy":[1,1],
            "full_nonvacuum_lowest_energy":[1,n],
        })
    # Given an arbitrary rational target B<1 at one physical length,
    # Bernoulli shows one can always choose n with q_n^n > B.
    for b in [Fraction(1,2),Fraction(9,10),Fraction(99,100),
              Fraction(999,1000),Fraction(9999,10000)]:
        n=max(2,b.denominator//(b.denominator-b.numerator)+2)
        lower=1-Fraction(1,n)
        assert lower>b
        # O(n log n) big-integer power is not needed to prove the
        # strict inequality; Bernoulli already gives q_n^n >= lower.
    return {
      "status":"PASS",
      "category":"exact countermodels / necessary-conditions audit",
      "ym_mass_gap_proved":False,
      "physical_unit_length_n":True,
      "strict_each_cutoff_contraction":True,
      "uniform_physical_exponential_rate_deducible":False,
      "one_selected_probe_controls_full_H_spectrum":False,
      "finite_tests":rows
    }

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--ns",default="2,4,8,16,32,64,128")
    parser.add_argument("--json")
    args=parser.parse_args()
    result=verify([int(v) for v in args.ns.split(",")])
    payload=json.dumps(result,indent=2)
    if args.json:
        with open(args.json,"w",encoding="utf-8") as f: f.write(payload+"\n")
    print(payload)

if __name__=="__main__":
    main()
