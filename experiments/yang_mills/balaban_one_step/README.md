# Finite Bałaban one-step laboratory

This directory computes finite SU(2) lattice objects used to formulate the
one-step RG problem: the gauge-covariant block average, gauge-fixed Wilson
Hessian, constraint kernel, conditional covariance, Gaussian log determinant,
finite polarization tensor, and fitted beta coefficient.

Every ordinary JSON result is labelled `finite_computation`. No script promotes
a volume-uniform, scale-uniform, history-uniform, continuum, or Clay claim.
Exact-rational certificates use the separate `rational_certificate` status.

A minimal run is:

```bash
python build_q_matrix.py --L 2 --block 2 --out out/Q.npy
python build_wilson_hessian.py --L 2 --Q out/Q.npy --out out/H.npy
python constrained_covariance.py --H out/H.npy --Q out/Q.npy --out-prefix out/c
python finite_logdet.py --H out/H.npy --Q out/Q.npy --out out/logdet.json
python random_walk_green.py --H out/H.npy --Q out/Q.npy --out-prefix out/walk
python polarization_tensor.py --L 2 --block 2 --out out/Pi.npy
python extract_beta.py --tensor out/Pi.npy --L 2 --out out/beta.json
python ward_residuals.py --tensor out/Pi.npy --L 2 --out out/ward.json
```

Further frontier probes include:

- `background_sweep.py`: coercivity and conditioning across small regular backgrounds;
- `history_stability.py`: finite beta variation across explicitly supplied histories;
- `nonlinear_background_fixed_point.py`: numerical contraction of a constrained nonlinear Wilson critical map;
- `certify_finite_matrix.py`: floating computation with explicit roundoff margin and inverse residual;
- `rational_ldlt_certificate.py`: exact rational LDLT positivity and determinant certificate;
- `DashenGrossSU2OneLoopOracle.py`: convention calibration only.

The canonical path and averaging convention is explicit in `common.py`. It is a
reference convention that must be compared term-by-term with the target CMP98
formula before being called source-exact.

## Evidence ladder

- exact Agda proof;
- exact rational or interval certificate;
- finite floating computation with residuals;
- conjecture or counterexample candidate.

A successful finite calculation does not inhabit the uniform beta conjecture.
Likewise, the Dashen–Gross reference value calibrates normalization but does not
prove Bałaban history stability.
