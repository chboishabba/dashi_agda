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

## 9 November continuation: original finite exponential same-object transport

New source owner `DASHI/Analysis/BishopOriginalNegativeLogFiniteExpCrossWeightTransportExact.agda` (commit `a709f36ab19f8259fd552f81dcde1b7e42af8eaf`), imported by all three canonical TOE roots.

For `F_N` the **actual** pinned original finite exponential and `E_N=F_N-(1-x)`, the new `originalFiniteExpCrossWeightIsOriginalErrorCrossWeight` proves by real-ring cancellation, for all `N,x,h`:

```
(1-x) F_N(x+h) - (1-x-h) F_N(x)
    = (1-x) E_N(x+h) - (1-x-h) E_N(x).
```

`originalFiniteExpCrossWeightIsResidualPlusDefect` then consumes the existing original ODE and division-free error-derivative receipts to establish the same left-hand side equals

```
h * [ x^N F_N(x) + (1-x)(q_E(N,x,h)-E_N'(x)) ].
```

This removes the opportunity to substitute a synthetic exponential or an unrelated error function in the next weighted mesh analysis. **It does not prove the source quotient modulus, positive reciprocal endpoint telescope, convergence to `1-x`, or terminal `OriginalBishopNegativeLogExponentialGap`.**

Remaining implementation sequence: (1) source uniform modulus for `q_E(N,x,h)-E_N'(x)` on `0<=x<=r<1` at fixed N; (2) positive Bishop reciprocal weighted finite telescope, preserving the modulus after refinement; (3) derive the integrated `r^(N+1)/((N+1)(1-r)^2)` bound, then source convergence/limit uniqueness; (4) Agda 2.9 transitive imports and TOE root typecheck. P1/P2/P3 still have the exact terminal obligations above.

Verification: source-written Agda and committed imports; no kernel acceptance receipt. No claim of P0–P3 closure.

## Further 9 November implementation: exact multi-cell P0 composition

New owner: `DASHI/Analysis/BishopOriginalNegativeLogCrossWeightCocycleExact.agda`, wired into `EverythingTOESymmetryResolved369`, `Unifier` and `Unified/Everything`. This reuses the original exp/log finite-stage owner and the preceding source-cross-weight module.

Write `w(x)=1-x`, `F_N(x)=exp_B(-L_N(x))`, `D_N(a,b)=w(a)F_N(b)-w(b)F_N(a)`. A source-written ring proof now establishes the *three-vertex weighted cocycle*

```
w(b) D_N(a,c) = w(a) D_N(b,c) + w(c) D_N(a,b).
```

The same file proves `D_N(a,b)` equals the original target-error determinant, and refines the cocycle to the two-cell residual identity for `y=x+h`, `z=y+k`:

```
w(y) D_N(x,z)
 = w(x)*k*(R_N(y)+w(y)*(q_E(y,k)-E_N'(y)))
 + w(z)*h*(R_N(x)+w(x)*(q_E(x,h)-E_N'(x))).
```

**Specific new reduction:** a two-cell normalized cross-weight endpoint is now an exact polynomial combination of *actual original source local residuals and the actual original source quotient defects*, without inserting or assuming an FTC/integral, arbitrary selected function or reciprocal. Repeated finite composition is supported algebraically by this three-vertex law; a general mesh-majorant/positivity theorem is still needed. No bound on the quotient defects was fabricated.

### Remaining terminal proof leaves (unchanged)

- **P0.1**: derive a compact-uniform `q_E(N,x,h)-E_N'(x)` modulus on the original Bishop carrier from the explicit finite polynomial quotient and shifted-factorial exponential series; avoid claiming `h->0` pointwise suffices uniformly.
- **P0.2**: prove positive weight/reciprocal monotonicity for all mesh vertices `x<=r<1`, then sum the cocycle without losing the quotient remainder.
- **P0.3**: produce the original Bishop sharp endpoint error and effective common stage cutoff, then use existing `originalNegativeLogTerminalFromFiniteEvaluation`.
- **P1**: original nested atan-to-complex-exp coefficient evaluation at `1/5`, `1/239` or equivalent constructive ODE uniqueness; rational Cayley evaluations alone are insufficient.
- **P2**: feed P0 to already-existing `BishopRiemannOriginalZetaAboveTwoExact.FromOriginalNegativeLog` and prove selected external/opaque zeta same-object value equality, not fiat.
- **P3**: genuine Gamma factor, prefactor, continuation, reflection and completed Xi same-object identification.

**Verification status:** new source declarations and three imports committed, exact branch file readback planned; `agda` executable unavailable in working container. No kernel acceptance or terminal P0/P1/P2/P3 discharge is claimed.

## 9 November: all-finite-mesh induction (P0 next implementation)

Committed original Agda source owner `DASHI/Analysis/BishopOriginalNegativeLogFiniteWeightedMeshRecurrenceExact.agda` (first commit `a591ed24fb65f7a67b57c1cb1960a0c9b395b4f6`). All three TOE root import graphs now consume it. This generalizes the earlier two-cell source cocycle to an **arbitrary finite** walk rather than adding a new selected integrating-factor record.

For `v_n = finiteWalk 0 steps n`, `w_n=1-v_n`, `F_N=exp_B(-L_N)` and `D_N(a,b)=w(a)F_N(b)-w(b)F_N(a)`, define

```
P_0 = 1; P_(n+1) = P_n * w_(n+1)
B_0 = D_N(v_0,v_1)
B_(n+1) = (P_n*w_0)*D_N(v_(n+1),v_(n+2)) + w_(n+2)*B_n.
```

The new source declarations state the fully quantitative *finite algebraic* endpoint equality

```
P_n * D_N(v_0,v_(n+1)) = B_n,
```

then recursively replace every local determinant by its **actual** original source residual-plus-quotient-defect,

```
D_N(v_j,v_(j+1)) = h_j * [v_j^N * F_N(v_j)
                          + w_j*(q_E(N,v_j,h_j)-E_N'(v_j))].
```

The terminal source-level consumer `originalFiniteSourceScaledEndpointIsResidualBudget` unifies these two recursions. No reciprocal, FTC, MVT, positivity premise, or derivative-limit substitution is smuggled into the finite induction.

This resolves the **all-cell algebraic accumulation** subgate, subject to kernel acceptance, but **not** the source quotient modulus. Exact terminal leaves now:

1. **P0.a**: Original same-stage compact-uniform factor-quotient defect estimate from `BishopOriginalNegativeLogFiniteExplicitQuotientExact` (finite LOG polynomial quotient × shifted-factorial exp quotient) with explicit dependence on stage, radius and increment.
2. **P0.b**: Prove positive `w_j` and quantitative inverse bounds on `0<=v_j<=r<1`; transform the algebraic weighted budget into the normalized endpoint estimate *without losing uniform control as the mesh is refined*. Be attentive to products `P_n` tending to zero: never divide by them without independent conditioning.
3. **P0.c**: Apply an actual constructive endpoint integration comparison to obtain `0<=E_N(x)<=r^(N+1)/((N+1)*(1-r)^2)` and a common effective convergence cutoff; apply `originalNegativeLogTerminalFromFiniteEvaluation`.
4. **P1**: Original nested atan-to-complex-exp evaluation at both `1/5` and `1/239`, using already verified finite polynomial and corrected odd/odd Cauchy-owner.
5. **P2**: Supply the P0 identity to `BishopRiemannOriginalZetaAboveTwoExact.FromOriginalNegativeLog` and prove original selected zeta same-object equality independent of its opaque substrate.
6. **P3**: Genuine source Gamma, prefactor, continuation and completed-Xi equality.

**Verification**: declaration and import readback, static holes/postulates check, plus exact-head Agda 2.9 test are separate gates. Source-only work may not be marked accepted until an Agda kernel receipt. This commit does not close P0/P1/P2/P3.

## P0.01/P0.03 original-source implementation pass (9 November 2026)

**Implemented source declarations, kernel acceptance still pending:**

- `DASHI/Analysis/BishopOriginalFiniteLogQuotientSecondOrderExact.agda`:
  `sourcePowerSecondQuotient`, `originalPowerQuotientSecondOrder`,
  `sourceFiniteLogSecondQuotient`, `originalFiniteLogQuotientSecondOrder`,
  `originalFiniteLogQuotientAtZeroIsDerivativePolynomial`, and
  `originalFiniteLogPolynomialQuotientExactDefect`.
  Last theorem proves for every N,x,h:
  `q_L,N(x,h) ≃ P_N(x) + h*S_N(x,h)`, where P_N is the actual
  `negativeLogDerivativePolynomial` and S_N is the explicit source
  reciprocal-weighted finite polynomial. This is algebraic *factorization*,
  **not** the requested compact-uniform inequality.
- `DASHI/Analysis/BishopOriginalFiniteLogExpQuotientDefectSplitExact.agda`:
  `originalFiniteLogErrorQuotientDefectSplit` states
  `q_E-d_E ≃ -F_N * [h*S_N*Q(delta) + P_N*(Q(delta)-1)]`,
  where delta is the actual source negative finite-log increment, Q is
  `Origin.originalExpOriginQuotient`, F_N is the original bishopExp
  of the actual finite partial. `originalSourceShiftedFactorialErrorBound`
  reuses the existing P0.02 majorant
  `ExpClosed.originalExpQuotientMinusOneAbsBound`, which proves
  `|Q(delta)-1| <= exp_B(|delta|)-1`.
- Both new modules imported into `EverythingTOESymmetryResolved369`,
  `Unifier` and `Unified/Everything`.

**Independent finite regression**: 1,377 exact-rational triples (N,x,h),
N=0..16, 9x9 rational grid, checked both power/log quotient recurrences,
the zero-step derivative equality, and the composite-defect algebra for
two independent rational selections of F,Q (2,754 composite checks).
The mathematical identity passes; these tests do not replace the Agda kernel.

**New sharpened next inequality target (not yet formalized)**: for
`0<=x,x+h<=r<1`, the finite polynomial S_N is nonnegative and its
coefficientwise upper bound satisfies

```
0 <= S_N(x,h) <= sum_{k=2}^N (k-1)*r^(k-2)/2
              <= 1/[2*(1-r)^2].
|q_L,N(x,h)-P_N(x)| <= |h|/[2*(1-r)^2].
```

This is uniform in N, not merely a fixed-N modulus. A Bishop-order proof
needs nonnegative finite powers, rational coefficient embedding,
`T_k <= binomial(k,2) r^(k-2)`, and the geometric derivative-square
majorant with positive apartness of 1-r. The original shifted-factorial
bound then controls the remaining `Q(delta)-1` term. No general FTC
assumption is introduced.

**Still unpaid:** make the above order bound Agda-kernel accepted;
control `|delta| <= |h|/(1-r)` and exp_B on the source compact;
combine both in the P0.03 error bound; positivity/conditioning of mesh
weights; actual normalized endpoint comparison and convergence to 1-x;
the independently selected original P1 Cayley evaluations, P2 same-object
zeta value, and P3 Gamma/continuation/xi. Do not mark them closed.

## Further P0 implementation: original positive reciprocals and all-cell normalized endpoint

New source owners (all imported into three canonical TOE roots):

- `DASHI/Analysis/BishopOriginalFiniteMeshPositiveGapExact.agda`
  provides `originalBishopMeshVertexRatio`, `originalBishopMeshWeightsPositive`,
  `originalBishopMeshWeightNonzero`,
  `originalBishopMeshWeightInverse`,
  `originalBishopMeshWeightInversePositive`,
  `originalBishopMeshWeightInverseCancels`.
  Consumes **existing** `BishopFiniteDegreeOneGeometricBoundExact`
  `BishopUnitIntervalRatio` and native `Inverse.*-inverseˡ`, requiring real
  supplied evidence that each original vertex lies in `[0,1)`.
  The **uniform inverse upper bound** for a radius `r<1` is not proved here.
- `DASHI/Analysis/BishopOriginalNormalizedExpIncrementExact.agda`
  proves `originalNormalizedFiniteExpCrossIsSourceCross`,
  `originalNormalizedFiniteExpIncrementIsResidualPlusDefect`,
  and `originalNormalizedFiniteExpUnweightedIncrement`.
  Let `G_N(x)=F_N(x)*inv(1-x)`; it establishes the exact *local* equality
  `G_N(x+h)-G_N(x) = inv(1-x)*inv(1-x-h)*h*(R_N(x)+(1-x)*(q_E-d_E))`.
- `DASHI/Analysis/BishopOriginalNormalizedFiniteMeshEndpointExact.agda`
  proves `sourceFiniteSequenceIncrementTelescope`,
  `originalNormalizedMeshIncrementIsResidualCell`,
  `originalNormalizedMeshResidualSumIsIncrementSum`,
  and `originalNormalizedFiniteMeshEndpointIsSourceResidualBudget`.
  For any finite original walk and a proof-bearing ratio for each vertex,
  this is the exact endpoint equality
  ```
  G_N(v_m)-G_N(v_0)
    = Σ(j<m) inv(1-v_j)*inv(1-v_(j+1))*h_j*
        [v_j^N F_N(v_j)+(1-v_j)*(q_E(N,v_j,h_j)-E'_N(v_j))].
  ```
  Every quotient and exponential is the *original pinned* one.

This **supersedes the older P_n product-weight algebra as the preferred
P0 endpoint route**: local inverses are bounded by one common
`inv(1-r)` when `v_j<=r<1`, whereas a mesh-wide product may
degenerate under refinement.

**What is and isn't paid:** P0.01 and P0.03 algebraic decompositions,
P0.04 exact pointwise reciprocal existence/cancellation and P0.05
finite normalized endpoint transport are newly source-written.
The following are still real mathematical obligations and *cannot*
be replaced by the above equalities: construct an actual Bishop-order
uniform S_N bound (proposed `S_N <= 1/[2(1-r)^2]`), an original
`|delta| <= |h|/(1-r)` bound, uniform exponential error control,
the reciprocal antitonicity/radius comparison, passage from finite
mesh quadrature to the proper endpoint majorant, the sharp stage error
bound and terminal convergence. P1 original two Machin analytic
equalities, P2 selected zeta semantics and P3 Gamma/continuation
remain independent open leaves. No Agda kernel receipt is claimed.

**No document-only gate can be marked an Agda theorem.** Run exact-head
Agda 2.9 typecheck of each new owner and transitive imports. In
particular examine native solver goal conversion and proof irrelevance
of the positive inverse witnesses.

## P0.02 compact-uniform original shifted-factorial bound (further 9 November)

Added `DASHI/Analysis/BishopOriginalShiftedFactorialUniformModulusExact.agda`
and wired it into all three canonical TOE roots. The theorem
`originalShiftedFactorialExpQuotientUniformModulus` directly composes
the already existing source owners
`ExpClosed.originalExpQuotientMinusOneAbsBound` and
`ExpMono.bishopExpMonotoneNonnegative`. It gives, with a genuine
nonnegative Bishop radius rho,

```
|u| <= rho => |Q(u)-1| <= bishopExp(rho)-1
```

for the **literal** original shifted-factorial source Q. The
`originalNegativeLogShiftedFactorialUniformModulus` specialization
feeds the *actual* finite LOG increment delta as u.

This is a uniform **argument-ball** bound. To produce a full mesh
modulus as h->0, combine the existing
`originalSourceNegativeLogDeltaIsSecondOrder` with a genuine original
Bishop radius estimate `|delta_N(x,h)|<=rho_N(h)`, uniformly over
the mesh compact. Do not mark P0.03 or terminal P0.06 complete merely
because P0.02's argument-ball comparison is source-written.

Independent exact-rational finite checks: 14,520 source second-order
modulus instances (N through 30, four r values, 11x11 endpoint grid)
and 14 normalized endpoint meshes passed. No Agda 2.9 kernel receipt
is available. Keep P1/P2/P3 semantic leaves unchanged.

## 2026-11-09 P0.01–P0.03 SOURCE-WRITTEN ANALYTIC MODULUS PASS

The following are **new concrete Agda definitions and proof terms** on the original pinned Bishop real. Each remains subject to Agda 2.9 kernel acceptance; static readback/regression is not such acceptance.

1. `BishopOriginalFiniteLogSecondQuotientPositiveExact.agda`:
   `originalPowerZeroStepQuotientNonnegative`,
   `originalPowerSecondQuotientNonnegative`,
   `originalFiniteLogSecondQuotientNonnegative`,
   `originalFiniteLogPolynomialQuotientDefectEqualsStep`,
   `originalFiniteLogPolynomialQuotientDefectNonnegative`.
   Nonnegative endpoint polynomials and positive-step source secant sign.
2. `BishopOriginalFiniteLogQuotientUniformModulusExact.agda`:
   `sourcePowerZeroQuotientMonotone`,
   `sourcePowerSecondQuotientMonotone`,
   `sourceFiniteLogSecondQuotientMonotone`,
   `originalFiniteLogPolynomialQuotientUniformModulus`.
   **Fixed-stage compact-uniform** original log quotient:
   ```
   0<=x,x+h<=r =>
   |q_L,N(x,h)-P_N(x)| <= |h| S_N(r,0).
   ```
   Handles negative h; no division by h. The stronger single
   N-independent bound `S_N(r,0)<=1/(2(1-r)^2)` remains **not
   implemented** in original Bishop order.
3. `BishopOriginalFiniteLogQuotientRadiusDominanceExact.agda`:
   `sourcePowerQuotientRadiusDominance`,
   `originalSourceFiniteLogQuotientRadiusDominance`,
   `originalNegativeLogIncrementAbsoluteIsStepTimesQuotient`,
   `originalNegativeLogIncrementUniformRadiusBound`,
   `originalFiniteLogRadiusDerivativeNonnegative`,
   `originalFiniteLogDerivativeRadiusDominance`,
   `originalFiniteLogShiftedFactorialStagewiseMeshBound`.
   Proves on nonnegative source endpoints `|Delta_N(x,h)|<=|h| P_N(r)`
   and `|Q(Delta_N)-1|<=exp_B(|h|P_N(r))-1`.
4. Existing `BishopOriginalShiftedFactorialUniformModulusExact.agda`
   strengthened by `originalShiftedFactorialAbsoluteBelowExpBall`:
   `|u|<=rho => |Q(u)|<=exp_B(rho)`, reusing original source
   monotonicity and the previously established
   `originalShiftedFactorialExpQuotientUniformModulus`.
5. `BishopOriginalFiniteLogExpQuotientTriangleExact.agda`:
   `originalFiniteLogErrorQuotientAbsoluteTriangle`,
   `originalFiniteLogErrorFirstTermRadiusBound`,
   `originalFiniteLogErrorSecondTermRadiusBound`,
   `originalFiniteLogErrorQuotientRadiusTriangle`.
   An actual source absolute-triangle proof for the original composite
   quotient defect, with no abstract "bound" field.
6. `BishopOriginalFiniteLogExpStagewiseUniformDefectExact.agda`:
   `sourceOriginalUniformErrorBudget`,
   `sourceOriginalUniformErrorBudgetNonnegative`,
   `originalFiniteLogExpStagewiseUniformDefectWithFactor`,
   `originalFiniteLogErrorQuotientUniformModulus`.
   For `N=suc n`, `0<x<=r`, `0<=x+h<=r`, source writes
   ```
   |q_E,N(x,h)-E_N'(x)| <=
      |h| S_N(r,0) exp_B(|h| P_N(r))
      +P_N(r)[exp_B(|h| P_N(r))-1].
   ```
   Stagewise uniform in x and the sign of h. Uses ORIGINAL
   `F_N(x)>0` and `F_N(x)<1`, not a synthetic exp.
7. `BishopOriginalFiniteLogExpUniformDefectNullModulusExact.agda`:
   `originalNullAbsoluteConvergesZero`,
   `originalNullScaledConvergesZero`,
   `originalNullExpOfScaledAbsConvergesOne`,
   `originalNullExpOfScaledAbsMinusOneConvergesZero`,
   `originalFiniteLogStagewiseUniformBudgetConvergesZero`.
   Source proof that the displayed common budget tends to zero
   for **every original null sequence h** at fixed degree/radius,
   via native Bishop exp continuity and Sequence product/sum laws.
8. `BishopOriginalNormalizedFiniteMeshEndpointExact.agda` gained
   `originalNormalizedFiniteMeshEndpointAbsoluteBudget`: actual
   `|G_N(v_m)-G_N(v_0)|<=sum_j |localOriginalResidualCell_j|`,
   using finite source `sumFiniteAbsoluteTriangle` without FTC.

All seven new mathematical source modules, the strengthened original
Q module and normalized endpoint are now imported (directly or
transitively) by `EverythingTOESymmetryResolved369`, `Unifier`,
`Unified/Everything`. The exact-rational first/second quotient and
modulus regression was executed against a matching source recurrence
for **10,164** cases (four radii, 11x11 endpoints, degrees 0..20);
all checks passed, including negative h. The script is committed as
`scripts/check_bishop_original_log_quotient_uniform_modulus.py`.
This supports the finite algebra only; **not an Agda receipt**.

### Next exact semantic leaves, not mere wrapper work

- `originalBishopMeshInverseDominatedByRadiusInverse`:
  derive `0<1-r<=1-v_j` and quantitative native Bishop
  `inv(1-v_j)<=inv(1-r)` for all actual mesh vertices, including
  proof-relevant inverses, from original order laws.
- `originalBishopFiniteNormalizedEndpointResidualComparison`:
  apply original `originalFiniteLogErrorQuotientUniformModulus` to
  the SOURCE normalized mesh summands and bound the forcing by
  `v_j^N F_N(v_j)`, maintaining one common modulus for all cells.
- `originalBishopFinitePowerQuadratureEndpointBound`:
  bound original finite quadrature of `t^N` by
  `x^(N+1)/(N+1)`, with a constructive finite-mesh refinement
  theorem; cannot introduce an uninhabited FTC.
- `originalFiniteNegativeLogExpUniformEndpointBound` and
  `originalNegativeLogFiniteEvaluationConvergesToOneMinus`:
  compose these to yield the existing
  `OriginalBishopNegativeLogExponentialGap` via original
  `originalNegativeLogTerminalFromFiniteEvaluation`.
- Independently, original analytic P1 Cayley nested composition,
  P2 selected-zeta same-object value identification and P3 original
  Gamma/continuation/Xi remain genuinely unpaid. Do not mark them
  closed merely because the conditional compilers exist.

## Verification boundary

The container lacks `agda` and `nix`, and this pass obtained no
exact-head Agda 2.9 kernel run. Direct GitHub readback and balanced
source delimiters are **not** kernel acceptance. The new P0.01/P0.03
declarations are *source-written with concrete proofs*, **not
confirmed accepted**; check their transitive Agda elaboration before
claiming a terminal closure.


## 2026-11-09 exact-branch reconciliation: source proof versus kernel receipt

The older “Next exact semantic leaves” paragraph above is historical and
must not be read as the current implementation status. Exact-head readback
now confirms the following concrete **source-written** declarations:

- `BishopOriginalFiniteNegativeLogExpEndpointBoundExact.originalFiniteNegativeLogExpUniformEndpointBound`:
  `|exp_B(-L_N(x))-(1-x)| <= inv(1-(x+1)/2)^2 * x^(N+1)/(N+1)`
  for original proof-bearing `0<=x<1`. The midpoint factor is
  `4/(1-x)^2`, weaker than the earlier desired compact-radius constant but
  sufficient for convergence.
- `BishopOriginalNegativeLogTerminalFromMeshExact.originalNegativeLogFiniteEvaluationConvergesToOneMinus`:
  consumes the stagewise endpoint bound, native power and reciprocal
  convergence, and vanishing-difference convergence.
- `BishopOriginalNegativeLogTerminalFromMeshExact.originalBishopNegativeLogExponentialGap`:
  feeds the actual source finite evaluation into the pre-existing
  `originalNegativeLogTerminalFromFiniteEvaluation`.
- `BishopOriginalZetaAboveTwoFromMeshLogExact.FromOriginalBishopMeshLog.originalAboveTwoZetaFromCompletedLog`:
  instantiates the original above-two Dirichlet construction with that
  LOG witness. This is P2.01 only, not selected external zeta equality.

The focused Agda workflow was amended to include these exact terminal
modules and their endpoint prerequisites as explicit targets; the three
canonical TOE root checks remain required. Missing `0ℚᵘ` scope imports
were corrected in the original finite-power quadrature, finite-error
equal-mesh comparison, normalized endpoint quadrature, and terminal LOG
source modules. These corrections are **not** proof of kernel acceptance.

### Current decisive cuts (do not re-list the already source-written P0 leaves)

1. **P0-V**: execute the pinned Agda 2.9 `--safe` checker over all
   changed terminal owners plus transitive imports and three TOE roots;
   repair actual compiler errors, and store exact-head kernel receipts.
2. **P1.01–P1.03**: prove a same-original-carrier analytic identity
   `exp_C(2 i atan_B(t)) = Cayley(t)` on the selected half-ball.
   The repository already supplies the source atan uniform tail,
   geometric finite derivative, derivative-limit cancellation,
   rational Cayley differential polynomial, formal coefficients, and
   pointwise rational phases. It does **not** yet exhibit the analytic
   composite coefficient/evaluation or constructive ODE uniqueness
   across the independently selected original series.
3. **P1.04–P1.05**: specialize that genuine result to the existing
   `OriginalAtanFiveCayleyEvaluation` and
   `OriginalAtan239CayleyEvaluation` targets; the downstream Machin
   first-zero consumer is already implemented.
4. **P2.02–P2.04**: re-use
   `BishopRiemannOriginalNatLogTermCoherenceExact` and
   `BishopRiemannDirichletBaselSameObjectExact` for termwise and
   majorant-independent original values. Equality with the separately
   selected `ZetaHalfPlaneLayer.zetaHalfPlane` remains semantically
   **underdetermined** by the current opaque interface: see
   `RiemannOpaqueZetaHalfPlaneCountermodelExact`. Add a real
   original-Dirichlet identification to the concrete selected
   implementation, not a free proof field or fiat.
5. **P3.01–P3.07**: the original Gamma Mellin construction, prefactor,
   meromorphic continuation, functional equation, factor equality,
   entireness and reflection are still genuine analytic work. The
   current Xi continuity compiler is conditional and the existing
   opaque completed-Xi countermodel rules out semantic closure by
   interface projection alone.

**Verification status**: GitHub source readback and workflow coverage
confirmed. No exact-head Agda kernel result, completion of the P1
analytic composition, independent selected-zeta equality, or P3
completed-Xi proof is claimed by this reconciliation.


## 2026-11-09 P1.01 forced formal coefficient uniqueness (source implementation)

New original carrier owner:
`DASHI/Foundations/BishopMachinCayleyEquationForcesCoefficientsExact.agda`;
imported by all three canonical TOE roots.

For any stream `c : Nat → RationalComplex`, define the literal coefficient
of `(1-iX) c` by `c₀` at degree zero and
`c_(n+1) - i*c_n` at degree `n+1`. The new proof constructs
`originalEquationForcesRecurrence`: assuming this coefficient agrees
at **every degree** with the original finite polynomial `1+iX`
automatically implies:

```
c₀ = 1;
c₁ = 2i;
c_(n+2) = i*c_(n+1).
```

Then `originalCayleyEquationCoefficientUnique` invokes the already
existing original canonical recurrence uniqueness theorem and proves

```
forall n, c n = BishopMachinOriginalCayleyFormalSeriesExact.cayleyFormalCoefficient n.
```

This discharges a stronger finite-algebra part of P1.01, removing any
independent recurrence assumption. The decisive **analytic** part of
P1.01/P1.02 remains: construct the coefficient stream of the actual
nested `exp_C(2i atan_B(t))`, show that its analytic composition has
the original denominator equation (with valid convergence/reindexing),
and then identify evaluation on the selected half-ball. Only after that
can the existing `OriginalAtanFiveCayleyEvaluation` and
`OriginalAtan239CayleyEvaluation` be inhabited. No assertion of
analytic completion or kernel acceptance is made by the new source.


## P1 algebraic expansion and stage-13 provenance boundary

Source owner: `DASHI/Foundations/BishopMachinCayleyFourCycleJanko13BoundaryExact.agda`.

New source-written statements (kernel check intentionally deferred):

- `originalCayleyCoefficientFourPeriod` proves the canonical Cayley
  rational-complex coefficients have `c_(n+5)=c_(n+1)` for all
  `n : Nat`; `c0=1` remains the exceptional constant term.
- `originalCayleyThirteenSameAsOne` and
  `originalCayleyThirteenIsTwoImaginaryUnits` prove `c13=c1=2i`.
- `originalEquationForcesFourPeriod` proves that ANY coefficient stream
  satisfying the previous original `(1-iX)F=1+iX` all-degree equation
  has that same four-period, by transporting the established unique
  coefficient identification; no independently supplied recurrence.
- `originalEquationForcesStage13Phase` specializes to stage 13.
- The existing `SecondRevolutionJankoTarotExact` supplies the
  independent exact ordinal charts `J3 -> 13=10+3=9+4`.
  Those are merely common Nat indices. The group, modular j function,
  principal modular level, stage carrier, and coefficient stream remain
  distinct typed objects; `JChartSuccessorBoundary` already
  enforces distinct chart/modular/representation roles.

This is a stronger finite-algebra slice of **P1.01** and a provenance-safe
index bridge. It is not `exp_C(2i atan_B(t)) = Cayley(t)`.
The remaining decisive original-source obligations are (a) derive the
same all-degree denominator identity from actual nested original
exp/atan coefficients with the justified Cauchy/reindex theorem, or
(b) prove a same-source ODE uniqueness theorem with full derivative
and initial-value transport; then (c) produce genuine convergent
half-ball evaluation and the two original pointwise witnesses.
P2 selected-zeta semantic equality and P3 Gamma/continuation/Xi
remain open independently.


## Cross-programme maximum cut: 13-coordinate hyperfabric / puncture

For the exact 12+1 and 9+3+1 fibre decomposition, constructive
zero-section/last-coordinate complement, globally punctured-origin
counterexample, canonical prefix-observer non-descent, source commit
receipts, and independently outstanding Bishop analytic work, see:

`Docs/roadmaps/BishopHyperform13PunctureMaxCut20261109.md`

Implementation owners:
`DASHI/Foundations/TernaryThirteenFibreSplitExact.agda`,
`DASHI/Foundations/TernaryThirteenFibrePunctureExact.agda`, and
`DASHI/Foundations/TernaryThirteenFibreObserverNonDescentExact.agda`.

The new finite-word proofs do not close the original-source
`centralCompletionIsThirteenTritFibre` equivalence, semantic
observer/gluing transport, Bishop P1 atan–exponential–Cayley
same-object identity, independently selected zeta equality or
Gamma/Xi construction.
