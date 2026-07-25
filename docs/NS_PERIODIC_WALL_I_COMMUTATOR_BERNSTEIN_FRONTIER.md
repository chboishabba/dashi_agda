# Periodic Wall-I commutator and cube-Bernstein frontier

This tranche narrows the remaining Wall-I work without manufacturing any of the cutoff-uniform PDE estimates.

## Far-low: exact energy commutator before absolute values

The formal dependency chain is:

1. `NSPeriodicFarLowEnergyPairingCancellation`
2. `NSPeriodicFarLowExactCommutatorIdentity`
3. `NSPeriodicFarLowMultiplierDifferenceKernel`
4. `NSPeriodicFarLowMultiplierDifferenceBound`

The first module proves the self-tested transport cancellation from the mixed periodic integration-by-parts identity and characteristic-zero double cancellation. It also makes the applicability restriction explicit: the advected shell and tested shell must be definitionally identified. A mixed pairing is only skew; its two terms do not vanish separately.

The second module proves

```text
<Delta_j(a . grad v), Delta_j v>
  = <[Delta_j,a . grad]v, Delta_j v>
```

from the literal field split and the self-pairing cancellation. No norm estimate enters this theorem.

The third module owns three distinct kernels:

```text
K_raw     = m_j(k) B(k,p,q)
K_diff    = (m_j(k)-m_j(q)) B(k,p,q)
K_absdiff = |m_j(k)-m_j(q)| |B(k,p,q)|
```

`K_diff` remains signed. `K_absdiff` is a separate object for absolute Schur analysis.

The fourth module proves the order-theoretic mean-value reduction:

```text
|m_j(q+p)-m_j(q)|
  <= gradientScale * distance(p,0)
  <= C_mv * separationFactor.
```

It then transports that bound through a nonnegative bilinear-symbol majorant. The concrete smooth profile gradient and the cutoff-uniform row/column sums remain conditional.

### Executable reconnaissance

Run:

```bash
python scripts/ns_periodic_wall_i_commutator_recon.py \
  --cutoff 4 --output-shell 2 --separation 2 \
  --target-separation 8
```

The script constructs the rational derivative/Leray/Biot-Savart tensor and compares:

- the absolute Schur diagnostic for `K_raw`;
- the absolute Schur diagnostic for `K_absdiff`;
- signed tensor aggregation for `K_diff`.

Signed aggregation is deliberately not called a Schur norm. The output also states whether the requested target separation is geometrically accessible at the chosen finite cutoff. In particular, a cutoff-four, output-shell-two run cannot test an actual `R=8` low/high separation.

Fast regression:

```bash
python scripts/test_ns_periodic_wall_i_commutator_recon.py
```

## Far-high: direct max-coordinate cube Bernstein route

The formal dependency chain is:

1. `NSPeriodicInfinityShellModeCount`
2. `NSPeriodicInfinityShellBernstein`
3. `NSPeriodicInfinityShellDerivativeBound`
4. `NSPeriodicFarHighOfficialPlacementReduction`

`NSPeriodicInfinityShellModeCount` reuses the repository's duplicate-free cutoff cube and proves the exact literal length of the outer cube at radius `2^n`. No Euclidean shell comparison is needed.

`NSPeriodicInfinityShellBernstein` separates:

- the exact finite mode count;
- finite Cauchy-Schwarz;
- shell Parseval;
- the optional coarse `2^(3n/2)` presentation.

The exact-count Bernstein reduction is checked. The finite Cauchy-Schwarz authority is standard imported analysis, while the concrete coarse constant remains to be identified on the official scalar carrier.

`NSPeriodicInfinityShellDerivativeBound` separates the elementary modewise inequality

```text
|k|_2^2 <= 3 * 2^(2n)
```

from the final square-root norm presentation.

`NSPeriodicFarHighOfficialPlacementReduction` replaces opaque placement fields with three explicit steps for each orientation:

```text
placement
  <= Leibniz/Leray majorant
  <= cube-Bernstein majorant
  <= official Sobolev shell-tail term.
```

It then constructs the existing `PeriodicFarHighTailInputs`. The hypotheses `s>5/2`, the official Sobolev conversion, and the structural constant derivation remain visible. The scalar tail arithmetic is still closed; the value eight is not frozen by this module.

## Near: proposition-valued first-exit smallness

`NSPeriodicFirstExitSmallnessInterface` distinguishes:

- `Admissible`, a proposition on index, time, and state;
- the dimensionless depletion observable;
- the theorem `Admissible -> depletion <= epsilonGamma`;
- each lane's analytic estimate in terms of depletion;
- the scalar budget comparison.

From those fields it derives the LH, HL, and HH canonical-share estimates by monotonicity and transitivity. The desired estimates are not stored as fields.

A separate candidate-observable record can name the topological-current, enstrophy, and inverse-vorticity factors without claiming that their product is small.

## Speculative geometric claims remain fail-closed

`NSPeriodicGeometricDepletionRejectionStatus` records that:

- exponential decay of the proposed topological current is not established;
- active-direction rigidity and the local alignment bridge are not established;
- the anti-congruence preimage argument is invalid as written;
- the congruence-allocation exclusion is invalid as written;
- the exponentially weighted superlinear ODE requires a quantitative threshold;
- the numerical preconditioner commutator and convex-building-set paper are unrelated to the periodic Wall-I proof obligation.

No rejected claim is exported as a proposition.

## Remaining analytic cutset

The branch still requires:

1. identification of the official Wall-I far-low pairing as a self-test;
2. a concrete smooth dyadic multiplier or an exact Lipschitz replacement with explicit profile constant;
3. cutoff-uniform control of the literal difference kernel by absolute Schur, signed/spectral analysis, or another operator norm;
4. the max-coordinate cube derivative and coarse Bernstein constants on the official norm carrier;
5. the far-high Sobolev conversion and resulting structural constant;
6. an independent theorem connecting first-exit admissibility to a dimensionless smallness coefficient.

The official sentinel remains:

```agda
allOfficialHarmonicInputsInhabited = false
```

No global regularity or Clay-promotion gate is changed.
