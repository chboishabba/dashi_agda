# Yang–Mills Round 42 — master-reconciled floor, fibre geometry and recovery

This note indexes the concrete theorem tranche on
`agent/ym-clay-alpha-round42-master-reconciled-floor-recovery`.
It is intentionally secondary to the Agda modules; the mathematical results
live in the theorem surfaces named below.

## Physical finite operator

The selected constraint remains the literal tagged operator

`L_A : Q^3072 -> Q^780`, with 12 block-average rows and 768 gauge rows.

The identity-background gauge transpose is proved pointwise to be the negative
periodic forward gradient. On componentwise-mean-zero gauge multipliers,

`actualFlatGaugeGramReducedFloor`

proves

`(1/16) ||lambda||^2 <= ||L_gauge,0^* lambda||^2`.

The selected-background forward defect estimate is converted into an adjoint
estimate by a literal finite Cauchy–Schwarz/Frobenius theorem. At
`rho = 1/8192`, the exact coefficient is

`3072 * 16 * (4 rho^2) = 3/1024`.

The finite perturbation identity then yields

`selectedBackgroundGaugeAdjointReducedFloor`:

`(29/1024) ||lambda||^2 <= ||L_gauge,A^* lambda||^2`

for every componentwise-mean-zero multiplier whenever the actual background
satisfies the repository's relaxed inverse-link radius.

## Stratified stabilizer geometry: the flat product fibre is false

`flatConstantRedundancyNotAutomaticallyTransported` gives an exact rational
small-radius holonomy counterexample. A constant Lie direction that is a flat
gauge zero mode is rotated by a non-central near-identity holonomy.

`selectedBackgroundStabilizerNeedNotEqualFlat` and
`nearIdentityStabilizerProfileExact` sharpen this into an orbit/stabilizer
statement. At the flat identity holonomy all three pure-quaternion basis
coordinates are fixed. For the literal rational near-identity holonomy about
the x-axis, x survives while both transverse y and z directions move.

Thus the intrinsic gauge symmetry object is stratified: the stabilizer type can
change with the background. It is not valid to trivialize the physical
redundancy as `background x Q^3` by deleting the three flat constant modes at
every selected background.

## Concrete flat based section and quotient asymmetry

`BalabanSelectedFlatGaugeBasedSectionExact` constructs an actual section of the
flat constant-shift quotient: for each Lie coordinate, subtract the value at the
literal base site `(0,0,0,0)`. It proves:

- the representative is based;
- the section is pointwise idempotent;
- every flat constant-shift class has a unique based representative;
- the actual flat selected gauge transpose is unchanged by replacing a
  multiplier by its based representative.

`basedSectionNotIdentityOnUnreducedCarrier` then exhibits a nonzero constant
multiplier whose based representative is zero. This is the concrete finite
asymmetry behind `pi o s = id` on quotient classes while `s o pi = id` is
false on unreduced representatives.

This theorem is intentionally a flat anchor. It is not promoted to a nonlinear
selected-background gauge-slice equivalence.

## Exact mean decomposition and full fixed-carrier regularized floor

`BalabanSelectedGaugeMeanDecompositionExact` decomposes every literal
768-coordinate multiplier as

`lambda = lambda_0 + P_const lambda`,

where `lambda_0` is componentwise global-mean-zero, and proves the exact
orthogonal identity

`||lambda||^2 = ||lambda_0||^2 + ||P_const lambda||^2`.

This permits a fixed regularizer without falsely calling it the moving physical
stabilizer. For the constant part `c = P_const lambda`, the flat adjoint is
exactly zero, so the physical selected-radius defect theorem gives

`||L_A^* c||^2 <= (3/1024) ||c||^2`.

Combining that estimate with the existing `29/1024` reduced floor and the
finite half-minus-defect inequality proves

`selectedBackgroundRegularizedGaugeFloor`:

`(29/2048) ||lambda||^2`
`  <= ||L_A^* lambda||^2 + ||P_const lambda||^2`

for every multiplier on the full fixed 768-coordinate carrier.

This is a new strict coercivity theorem on the complete fixed carrier. The
projector is a flat-reference regularizer, not an assertion that constant modes
are the true background stabilizer.

## Exact flat Green and exact background operator decomposition

`regularizedFlatGaugeGramIsConfiguredSiteOperator` proves that adding the
constant-mode projector to the actual flat gauge Gram gives the repository's
configured scalar operator `-Delta_periodic + P_const` componentwise.

`regularizedFlatGaugeGreenLeftInverse` and
`regularizedFlatGaugeGreenRightInverse` transport the existing explicit
256-site scalar Fourier Green kernel to a three-component two-sided
multiplier-space inverse.

`BalabanSelectedBackgroundGaugeOperatorDecompositionExact` now expands the
actual physical selected matrix itself. With

`D_A = L_A - L_0`,

it constructs the literal three-term perturbation

`E_A = L_0 D_A^* + D_A L_0^* + D_A D_A^*`

and proves pointwise

`selectedBackgroundBasedGaugeOperatorDecomposition`:

`K_A^reg = K_0^reg + E_A`.

Here `K_0^reg` is exactly the operator inverted by the existing Fourier Green;
`E_A` is computed from the actual selected gauge-defect matrix rather than
supplied as an unrelated perturbation receipt.

## The regularizer cancels: `E_A` is still local

A possible concern with the fixed regularizer is that `P_const` is spatially
nonlocal. `BalabanSelectedBackgroundGaugePerturbationFiniteRangeExact` removes
that obstruction exactly.

Because the same `P_const` is added to both the flat and selected-background
Gram,

`(K_A + P_const) - (K_0 + P_const) = K_A - K_0`.

`regularizerCancelsFromBackgroundDifference` proves this entrywise. The actual
selected-background and flat Gram matrices already share the same literal
finite row stencil, so

`regularizedGaugeGramDifferenceOutsideRangeZero`

proves that every perturbation entry between disjoint gauge-row stencils is
exactly zero. Thus the `E_A` entering the Green expansion is local. The next
problem is quantitative weighted smallness, not restoration of locality.

## Continuum lower-gap route

`vacuumOrthogonalRecoveryTransfersUniformGap` lifts the corrected Mosco-upper
inequality to a proof-carrying vacuum-orthogonal family. It needs only a
vacuum-compatible recovery vector with recovered norm and an energy upper
bound; it does not require trace-norm convergence of the entire transfer
operator merely to preserve a quadratic-form lower gap.

## Highest-alpha frontier after this tranche

The finite gauge problem is now narrower than at the start of Round 42. We have
an exact flat quotient section, an exact proof that the physical stabilizer is
stratified, a strict selected-background regularized floor on all 768
multipliers, an explicit flat Green, the exact physical decomposition
`K_A^reg = K_0^reg + E_A`, and exact finite range of `E_A`.

The nearest genuine analytic task is therefore the sharp weighted estimate on
the displayed local `E_A` needed to show

`||G_0 E_A||_mu < 1`

or an equivalent localized-parametrix contraction. Once that estimate is
proved, the existing finite Neumann/Combes–Thomas machinery can construct the
background Green and its exponential decay.

The nonlinear physical statement that a chosen based/global/tree gauge is a
section of the actual selected variational orbit is still separate. It must be
proved before a fixed gauge representative is identified with the physical
selected variational problem; the flat section above does not manufacture that
equivalence.

After the background Green, the next local steps are actual-minimizer
stationarity and the remaining literal Wilson/source-owner producer needed by
the existing `1/32` Hessian endpoint.

Beyond finite volume, the attached roadmap correctly reaches a genuinely open
four-dimensional constructive-QFT frontier: scale-uniform RG including the
large-field sector and observable transport, continuum Schwinger functions and
OS positivity, physical-time clustering/gap transfer, nontriviality/asymptotic
freedom, and finally compact-simple-group uniformization. These are not
represented here as completed by interfaces or proof-status labels.

No Clay completion or continuum Yang–Mills construction is asserted here.
