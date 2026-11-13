# Original L1: small-adjoint Haar analytic tail, with explicit source boundary

13 November 2026 · Agda PR #1498 · auxiliary mathematical lemma; **not** a
physical Ward-scalar or Clay completion.

## Existing owners to reuse

- `BalabanP0SU2HaarQuarticFormalJetExact.agda`: genuine formal SU(2)
  density/action jet signs (but not an analytic remainder).
- `BalabanCompactSimpleHaarQuadraticCasimirExact.agda`: classified compact-simple
  adjoint quadratic coefficient, with physical Haar chart identification open.
- `BalabanCMP109CompactSimpleColourReductionSourceExact.agda`: colour-scalar
  reduction (imported source analysis), not evaluation of the physical scalar.
- `BalabanP0LiteralIndexedTensorWardSourceExact.agda`: four-sector indexed Ward
  expression, without physical numerator evaluation.
- `BalabanClayHighestAlphaRound84SixAnalyticLemmaExact.agda`: full L1 requires
  both same-source one-loop value and a cutoff-uniform nonlinear remainder.

## Analytic local-chart proposition

Let `r` be real, `|r| <= 1`, and define `sinc(x)=sin(x)/x` with `sinc(0)=1`.
Then

```
0 <= -2 log(sinc(r/2)) - r^2/12 - r^4/1440 <= r^6/56700.
```

Proof. Euler's sine product, for `|r|<2 pi`, gives a convergent series

```
-2 log(sinc(r/2))
 = sum_{k>=1} [2 zeta(2k)/(k (2 pi)^(2k))] r^(2k).
```

The first two terms are exactly `r^2/12` and `r^4/1440`.
Every remaining term is nonnegative. For `k>=3`, the integral test gives
`zeta(2k)<=1+1/(2k-1)<=6/5`; also `pi>=3`, `k>=3`.
Thus the k-th coefficient is at most `(4/5)36^(-k)`. Therefore

```
R6(r) <= (4/5) * sum_{k>=3} r^(2k)/36^k
      <= (4/5) * (r^6/36^3) / (1-1/36)
       = r^6 / 56700.
```

The `r=0` case follows by continuity.

## Adjoint compact-simple corollary

Let `G` be compact connected semisimple. Equip its Lie algebra with an
invariant positive metric; let `ad_X` be skew-adjoint with nonzero
eigenvalues in pairs `+/- i lambda_j`. Assume `rho=max |lambda_j| <=1`.
In these exponential coordinates,

```
J_exp(X) = product_j sinc(lambda_j/2)^2.
-tr(ad_X^2) = 2 sum_j lambda_j^2 = C_A ||X||^2.
```

The previous bound applied to every pair gives

```
0 <= -log J_exp(X) - C_A ||X||^2/24
   <= (1/1440 + 1/56700) sum_j lambda_j^4
    = (323/453600) sum_j lambda_j^4
   <= (323/907200) C_A rho^2 ||X||^2.
```

This estimate is **mathematically derived from the standard Euler product,
adjoint skew-spectrum, and Jacobian formula**, not from an arbitrary
`SUNMatrixRealTrace` interface.

## Precisely what is *not* discharged

1. Show that the literal Bałaban gauge-fixed link/background chart on the
   original Wilson/FP/Haar carrier equals this exponential Jacobian, including
   its chosen colour metric and orientation.
2. Verify the entire finite-cutoff action/FP normalization and the four
   original indexed numerators; the ghost and Wilson contributions do not
   follow from Haar alone.
3. Prove the summed remainder with UV/volume/scale-uniform bounds. A
   pointwise per-link bound can accumulate with the number of links and is
   not itself a uniform RG estimate.
4. Obtain a pinned Agda 2.9 checker receipt for the new rational arithmetic
   module; no Agda binary was available in this environment.

## Reproducibility

- `DASHI/Physics/YangMills/BalabanP0HaarSmallAdjointChartRationalBudgetExact.agda`:
  two exact-rational equalities, no analytic or physical promotion.
- `scripts/check_balaban_l1_adjoint_haar_local_tail.py`:
  exact fractions `(1/1440+1/56700=323/453600)`, the half-Casimir factor,
  and five independent numerical SU(2) diagnostics.

**Original seven-obligation cut:** L1 remains open. R84 packages L6/L7 into
one physical stress-generator theorem; R475/R527 refine C source packages
without constructing the original physical source.
