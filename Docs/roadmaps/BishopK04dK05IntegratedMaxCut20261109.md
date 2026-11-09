# Bishop K04d/K05: original-source maximum cut (9 November 2026)

## Status and ownership

This note supplements the existing Bishop K04d/K05 roadmap; it does **not** assert any new Agda kernel receipt. Target branch: PR #1408. Preserve Bishop/Bridges and the pinned Murray/Csimma original Bishop real owner, with DASHI finite-stage derivative and source-quotient authors distinct. Do not modify ESD surfaces.

Original source owners already inspected at commit `e25598e7418e74b4d59b38edb7ff7d0cd53ecec0`:

- `DASHI/Analysis/BishopOriginalNegativeLogFiniteErrorDerivativeExact.agda`: actual source error `E_N`, quotient, initial value and finite ODE.
- `DASHI/Analysis/BishopOriginalNegativeLogCrossWeightedIncrementExact.agda`: exact division-free local integrating-factor cross-product and explicit quotient defect.
- `DASHI/Analysis/BishopOriginalNegativeLogFiniteExpMeshEndpointExact.agda`: original finite mesh exact endpoint identity and absolute error budget.
- `DASHI/Analysis/BishopOriginalFactorIncrementFiniteTelescopeExact.agda`: finite constructive telescoping, **not** yet a uniform differentiable endpoint theorem.

## P0: rigorous mathematical target, with stronger rate

Let `L_N(x) = sum_{k=1}^N x^k/k`, `F_N(x)=exp_B(-L_N(x))` and `E_N(x)=F_N(x)-(1-x)`. At each finite N the existing original-source identity is

```
(1-x) E_N'(x) + E_N(x) = x^N F_N(x),  E_N(0)=0.
```

For fixed constructive real `0 <= r < 1` and `0 <= x <= r`, once the original Bishop positive reciprocal / finite endpoint integration is installed, define `G_N(x)=E_N(x)/(1-x)`. The product and quotient laws yield

```
G_N'(x) = x^N F_N(x)/(1-x)^2,  G_N(0)=0.
```

Using the already source-derived `0 <= F_N(x) <= 1` on the interval, positivity and monotonicity give

```
0 <= G_N(x) <= x^(N+1)/((N+1)*(1-r)^2).
0 <= E_N(x) <= x^(N+1)/((N+1)*(1-r)^2)
             <= r^(N+1)/((N+1)*(1-r)^2).
```

The displayed bound is a *mathematical proof target* over ordered reals using interval integration, **not** an Agda theorem and not a claim that a Bishop FTC instance currently exists. It improves the previous proposed bound `x*r^N/(1-r)^2` by integrating the original power `t^N` exactly. In a constructive implementation, division by `1-r` needs an explicit positive apartness witness; `N+1` is a positive natural rational.

### P0 exact code cut

1. Locate and reuse the real positive reciprocal, real power endpoint-integral and differentiable product / quotient owners. The Marx integration bridge has an FTC law **as a field**, so it cannot be used until concretely inhabited on the same `Real.ℝ` and source derivative.
2. Prove a same-source finite-mesh quotient modulus strong enough to pass the finite cross-weighted telescope to the endpoint, **or** furnish a concrete Bishop interval integration instance for the finite function `G_N`. Do not identify derivative slopes with positive-step quotients without the modulus.
3. Kernel-check the original Bishop endpoint inequality above; send the uniform `N -> infinity` convergence through the existing original finite-stage limit uniqueness witness to inhabit `OriginalBishopNegativeLogExponentialGap`.
4. Do a pinned Agda 2.9 kernel run on the changed module and transitive imports and then the three TOE roots. Static absence of holes/postulates is insufficient.

**Avoid circularity:** the forcing `x^N F_N(x)` alone does not control `E_N'(x)`; the error term in the ODE cannot be dropped. The normalized integrating factor is precisely what cancels it.

## P1: two-point Cayley/atan max-cut

For each `t in {1/5,1/239}`, the required *analytic* identity is

```
exp_C(2 i atan_B(t)) = (1+i*t)/(1-i*t).
```

The rational target values are already present: `12/13 + 5i/13` and `28560/28561 + 239i/28561`. The exact remaining Agda work is to prove the original atan-series derivative and original complex exponential chain rule on the same carrier, then prove the derivative of `H(t)=exp_C(2i atan_B(t))*(1-it)/(1+it)` vanishes and `H(0)=1`. This is an alternative to all-degree series convolution but still requires constructive uniqueness/endpoint machinery, and no zero-derivative theorem is claimed here. Consume existing corrected grouped-parity boundary terms rather than reinstating an invalid naive Cauchy convolution. Then inhabit `OriginalAtanFiveCayleyEvaluation` and `OriginalAtan239CayleyEvaluation`.

## P2: above-two zeta same-object maximum cut

After P0, instantiate the original source-native `Re(s)>2` Dirichlet series using existing local convergence / Basel domination. Separately identify it with the **independently selected** `ZetaHalfPlaneLayer.zetaHalfPlane`; do not set an opaque field by fiat. The previously identified opaque-zeta countermodel shows why an arbitrary Set-valued layer does not prove analytic equality.

## Verification cut

| Gate | At this revision | Terminal kernel obligation |
| --- | --- | --- |
| P0 | Original finite ODE, initial value, source quotient and cross-weight identity exist; sharpened endpoint target specified | Concrete same-Bishop endpoint estimate and `OriginalBishopNegativeLogExponentialGap` |
| P1 | Exact rational Cayley values exist | Original analytic two-point atan-to-exp identities |
| P2 | Above-two convergence infrastructure and conditional construction exist | Actual original Dirichlet instantiation plus independent selected-function equality |
| P3 (downstream) | Continuity/factor compiler partial | Genuine Gamma/prefactor, analytic continuation and completed-Xi same-object weld |

No new theorem files, kernel check or P0/P1/P2 closure is claimed by this roadmap-only commit.
