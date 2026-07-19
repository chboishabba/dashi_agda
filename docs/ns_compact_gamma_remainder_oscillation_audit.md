# Compact-Gamma remainder-oscillation audit

> Status: finite Galerkin proof search and conditional Agda composition. Non-promoting.

## Purpose

The common-upper audit introduced the integrated remainder

`C_theta = integral max(R_K - theta E_K, 0) d tau`

and the member upper `B_K(t0) + C_theta`. Its first declared family was pointwise absorbed, so `C_theta` was zero throughout. This lane makes that term nontrivial.

Center profiles alone fit `theta` and `c_lambda`. Calibration and held-out profiles are deterministic perturbations of the normalized multi-triad packet class. They vary phase spread, target ratio, satellite strength, and seed while preserving positive amplitudes and a fixed target-packet energy.

At every resolved state the audit records the positive excess `max(R_K - theta E_K, 0)` and integrates it in parabolic time. A positive pointwise excess is treated as an explicit remainder contribution rather than silently converted into a failed or successful theorem.

## Finite-net test

The audit fits a one-sided change in integrated remainder against physical Fourier-state L2 distance on calibration profiles. It then tests the resulting center-plus-allowance upper on held-out profiles and matched N32/N48/N64 representations of the most adverse held-out perturbation.

The fitted slope is an experimental observable, not an analytic continuity estimate. The actual mathematical target is a shell- and cutoff-independent local-oscillation bound for the integrated remainder on a normalized packet class.

## Agda composition

`NSCompactGammaRemainderOscillationComposition.agda` represents one time block by

`memberRemainder <= centerRemainder + oscillationAllowance`.

It proves that two controlled blocks compose to a controlled sum with the center remainders and allowances added. Iteration supplies the finite-grid algebra once local analytic block estimates are available.

## Running

```bash
python scripts/ns_compact_gamma_remainder_oscillation_audit.py \
  --output-json /tmp/ns-compact-gamma-remainder-oscillation.json \
  --search-cutoff 24 --verify-cutoffs 32,48,64 \
  --target-shells 2,3 --target-packet-energy 0.86 \
  --triad-counts 4 --phase-spreads 0.0 \
  --target-ratios 2.5 --satellite-fractions 0.55 \
  --center-seeds 1 --calibration-seeds 2 --holdout-seeds 3 \
  --samples-per-base 4 \
  --calibration-jitter-scale 0.7 --holdout-jitter-scale 1.0 \
  --phase-jitter 0.8 --log-ratio-jitter 0.5 \
  --log-satellite-jitter 0.35 \
  --gamma-threshold 0.5 --theta-slack 0.005 \
  --c-lambda-slack 0.05 --slope-slack 0.15 \
  --end-parabolic-time 0.004 --output-count 3 \
  --verify-count 1 --pretty
```

The output remains finite-dimensional and non-promoting. It does not establish continuum compactness, BKM continuation, global regularity, or a Clay result.
