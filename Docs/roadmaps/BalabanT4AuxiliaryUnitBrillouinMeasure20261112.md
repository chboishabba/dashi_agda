# Bałaban T4 P0: source-normalized auxiliary Wilson four-orbit certificate

**Date:** 12 November 2026. **Owner:** Agda #1498. **Status:** numeric/rational exact validation PASS; new Agda module SOURCE-WRITTEN / KERNEL-OPEN; full physical one-loop beta and Clay E1/D1/D2/N1/G1 OPEN.

## Exact source identity and unit measure

The source grid is `DASHI.Physics.YangMills.BalabanClayT4GeneratedBrillouinGridExact` on `x∈[-1,1]^4`, partitioned into 256 cells of side 1/2. Geometric `cellVolume=1/16` is a volume in **x coordinates**, not a probability weight.

For the standard lattice momentum convention `k=πx` and `d^4k/(2π)^4`:

```
d^4k/(2π)^4 = d^4x/16.
source dx cube volume = 16.
unit-total mass of all 256 cells = 256 * (1/16) * (1/16) = 1.
infrared 16-cell mass = 1/16.
regular 240-cell mass = 15/16.
```

Thus the source-owned quadrature weights `4,6,4,1` for outer-rank `m=1,2,3,4` sum to **15**, not a total-mass-one integral. A second **1/16 factor** is needed to interpret them as a probability-normalized Brillouin integral. This is only a measure-convention normalization, not a statement that the original Wilson physical scalar has been identified.

## Actual source four-representative free propagator

Reuses without replacement:
- `BalabanClayT4RefinedSineSquareRegularBoxesExact.sourceWilsonDenominatorBox`;
- `BalabanClayT4FourAuxiliaryWilsonPropagatorBoxesExact.inverseOne` through `inverseFour`, and source exact endpoint equalities;
- `BalabanClayT4HypercubicOrbitQuadratureWeightsExact`.

On a regular cell with outer rank m≥1, **conditional on physical sine interval membership**, its unshifted free Wilson propagator has an endpoint interval:

```
1/16 ≤ 1 / hat(k)^2 ≤ 4096/(7569 m).
```

A direct exhaustive exact-rational 256-cell computation gives:
- un-normalized 240-cell x-volume lower `15/16`;
- un-normalized 240-cell x-volume upper `105472/22707`;
- correctly unit-normalized regular lower `15/256`;
- correctly unit-normalized regular upper `6592/22707`.

The new Agda module `BalabanClayT4AuxiliaryWilsonNormalizedMeasureExact` proves these **rational source normalisation and endpoint identities** by consuming original source constants and `Ring.solve-∀`; it does **not** prove integral monotonicity or the original physical sine memberships. Under actual pointwise membership and a correct integrability argument, the same interval endpoints would become an enclosure of the **regular-region free propagator integral**. The 16-cell infrared region is excluded.

## Local verification (no CI)

```bash
python3 scripts/check_balaban_t4_auxiliary_unit_brillouin.py
AGDA_JOBS=1 DASHI_NO_TMUX=1 bash scripts/run_agda29_parallel_check.sh DASHI/Physics/YangMills/BalabanClayT4AuxiliaryWilsonNormalizedMeasureExact.agda
```

The 256-cell and rational constant checks were independently executed in the current session and PASS. Exact-head repository-script replay and Agda 2.9 elaboration require the actual source checkout, Agda and standard library; these are **not** reported as passed.

## Exact remaining maximum cut

**Source/semantic welds:** original literal scalar `LiteralScalarIntegrandExpression` for gauge/ghost/tadpole/Haar on actual (SU(N)); correct source `k=πx` and per-box Fourier/Machin/Bishop sine membership; shifted/external denominator positivity, and the *actual* momentum covariance group (potentially only fixed-axis stabilizer, not all B4).

**Analytic certificates:** full numerator/denominator interval semantics; four actual source box integrals with true interval or Taylor/Hessian remainder, correct error covariance under the chosen group; singular/regular split and infrared cancellation; physical (b_0) and normalization. A tight range by itself supplies a coarse integral enclosure if the physical integrand is integrable, but not a narrow high-accuracy midpoint quadrature certificate.

**Clay physical mathematics remains independent:** original varying-cutoff full interacting Wilson continuum E1; uniform full Wilson covariance/OS clustering D1; same-H full nonvacuum gap D2; non-Gaussian/nontrivial continuum N1; complete physical group coverage G1. Finite free-propagator intervals do not establish any one of them.

**Attribution:** Wilson (1974), Faddeev–Popov (1967), Bałaban (1987), source owners in Agda #1498. The added result is the normalized endpoint coefficient check, not a newly established nonperturbative Yang–Mills theorem.
