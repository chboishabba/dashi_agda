# Buffered compact-Gamma danger-expenditure modulus

> Status: finite Galerkin proof search and conditional Agda reduction. Non-promoting.

## Motivation

The perturbed remainder audit found that the center-fitted lower bound

`Gamma_K >= lambda  =>  E_K >= c_lambda`

did not survive the held-out normalized packet family. The escape supply can decrease as the packet moves away from a finite-net center.

The correct local statement needs two moduli. For a member state `u`, nearby center `v`, and packet distance `d`:

```text
Gamma(u) - Gamma(v) <= L_gamma d^alpha
E(v) - E(u)         <= L_escape d^alpha
```

Member danger therefore transfers to a buffered center threshold. A center lower bound at that threshold loses only the escape allowance:

```text
lambda_center = lambda - delta_gamma
c_member      = c_center - delta_escape
```

The audit fits several Holder exponents on calibration profiles, checks them on held-out profiles, and rechecks the most adverse held-out state at N32/N48/N64 for shells 2 and 3.

## Agda theorem

`NSCompactGammaBufferedDangerExpenditure.agda` proves the abstract composition. Given:

- member danger transfers to buffered center danger;
- buffered center danger forces `centerLower <= centerEscape`;
- `centerEscape <= memberEscape + allowance`;
- `centerLower = memberLower + allowance`;

then

`memberLower <= memberEscape`.

No numerical distance, Holder exponent, or fitted constant is promoted into the theorem.

## Running

```bash
python scripts/ns_compact_gamma_danger_expenditure_modulus_audit.py \
  --output-json /tmp/ns-compact-gamma-danger-modulus.json \
  --search-cutoff 24 --verify-cutoffs 32,48,64 \
  --target-shells 2,3 --target-packet-energy 0.86 \
  --triad-counts 4 --phase-spreads 0.0 \
  --target-ratios 2.5 --satellite-fractions 0.55 \
  --center-seeds 1 --calibration-seeds 2 --holdout-seeds 3 \
  --samples-per-base 4 \
  --calibration-jitter-scale 0.7 --holdout-jitter-scale 1.0 \
  --phase-jitter 0.8 --log-ratio-jitter 0.5 \
  --log-satellite-jitter 0.35 \
  --gamma-threshold 0.5 \
  --holder-exponents 1.0,0.75,0.5,0.25 \
  --modulus-slack 0.15 \
  --end-parabolic-time 0.004 --output-count 3 \
  --verify-count 1 --pretty
```

A surviving finite exponent identifies a concrete regularity target for the packet observables. Failure identifies whether the obstruction is the Gamma buffer, escape oscillation, or loss of a positive residual lower bound. The continuum, compactness, BKM, and global-regularity bridges remain open.
