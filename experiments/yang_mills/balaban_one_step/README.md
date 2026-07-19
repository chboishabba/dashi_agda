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

## Local-parametrix search

`local_parametrix_search.py` constructs and compares finite-range approximate
inverses made from local Hessian restrictions. The available patch families are:

- isotropic cubes;
- unions of axis-oriented slabs;
- translated torus L1 balls of fixed radius.

The glued operator uses a symmetric diagonal partition of unity. A candidate is
reported as convergent only when both residuals satisfy

```text
||I - A G*||_mu < 1
||I - G* A||_mu < 1
```

in the requested exponentially weighted row norm. Spectral radius below one
without these norm inequalities is retained as an obstruction, not promoted.
The full-volume patch is reported separately and never counted as proper-local.

For the current `2^4`, block-two finite example, the search found:

- axis slabs close the trivial-background remainder but not the sampled
  nontrivial-background weighted norm;
- radius-two and radius-three torus balls are proper finite patches and close the
  sampled small backgrounds through radius `0.03` in the current test set.

Run the full finite search with:

```bash
python local_parametrix_search.py \
  --L 2 --average-block 2 \
  --local-sides 1,2 --slab-thicknesses 2 --ball-radii 2,3 \
  --mus 0,0.05,0.1 --radii 0,0.01,0.03 \
  --relaxations 0.25,0.5,0.75,1 --seeds 1 \
  --out out/local-parametrix-search.json
```

This is theorem-discovery evidence for the shape of a local random-walk proof.
It does not prove that one fixed patch radius, weight, or remainder constant
works uniformly in total volume, RG scale, or every admissible background.

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
