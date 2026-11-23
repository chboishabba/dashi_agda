#!/usr/bin/env python3
"""Exact-source prior sensitivity for Transparent Psi 2023.

The ORIGINAL analysis script at
  kekecsz/Transparent_psi_RR_materials/TPP_Statistical_analysis_script_FINAL.R
explicitly uses y_prior=828, N_prior=1560, BF01>=25, stop N=37836 and
a beta(a,b) restricted to p>.5 for the replication hypothesis.
Uploaded Bem EXP1.xlsx SHA256 feadd752... yields 826/1560 pooled hits.
The transparent-psi paper gives the RATE rounded to 49.89%, not an
unrounded exact hit count. Evaluate EVERY integer compatible with
that rounded rate, holding the original stop point unchanged.

Independent Python/SciPy numerical calculation, NOT Agda's own
infinite-series proof; does NOT reproduce the raw 2023 trial dataset
or mixed-effects logit.
"""
from __future__ import annotations
from math import exp, log
from scipy.special import betaln
from scipy.stats import beta

N_STOP = 37836
PUBLISHED_PRIOR = 828
EXP1_WORKBOOK_PRIOR = 826
ORIGINAL_PRIOR_N = 1560
BF01_STOP_THRESHOLD = 25

def compatible_successes(n=N_STOP):
    # Standard nearest-two-decimal percent gives [49.885,49.895)%.
    return [y for y in range(n+1)
            if 49885*n <= y*100000 < 49895*n]

def bf01_restricted_beta(y,n,y_prior,n_prior=ORIGINAL_PRIOR_N):
    a,b = y_prior+1, n_prior-y_prior+1
    # BF01 = L(y|p=.5)/E[L(y|p)|p>.5, Beta(a,b)]
    # Binomial coefficient cancels.
    log_bf = (-n*log(2) + betaln(a,b) - betaln(a+y,b+n-y)
              + log(beta.sf(.5,a,b))
              - log(beta.sf(.5,a+y,b+n-y)))
    return exp(log_bf)

def main():
    possible=compatible_successes()
    assert possible==[18875,18876,18877,18878]
    print("2023 aggregate rate 49.89% permits y =",possible)
    for y in possible:
        published=bf01_restricted_beta(y,N_STOP,PUBLISHED_PRIOR)
        workbook=bf01_restricted_beta(y,N_STOP,EXP1_WORKBOOK_PRIOR)
        assert 179 <= published <= 184
        assert 142 <= workbook <= 147
        assert min(published,workbook) > BF01_STOP_THRESHOLD
        print(f"successes={y} BF01(828)={published:.6f} BF01(826)={workbook:.6f} fraction={workbook/published:.6f}")
    print("PASS all source-compatible integer y retain BF01>25; prior correction changes BF by ~20%, not decision")
if __name__=="__main__":
    main()
