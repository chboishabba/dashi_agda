# Yang–Mills Round 42 — master-reconciled floor, fibre geometry and Green contraction

This note indexes the concrete theorem tranche on
`agent/ym-clay-alpha-round42-master-reconciled-floor-recovery`.
It is intentionally secondary to the Agda modules; the mathematical results
live in the theorem surfaces named below.

## Physical finite operator

The selected constraint remains the literal tagged operator

`L_A : Q^3072 -> Q^780`, with 12 block-average rows and 768 gauge rows.

The identity-background gauge transpose is proved pointwise to be the negative
periodic forward gradient. On componentwise-mean-zero gauge multipliers,
`actualFlatGaugeGramReducedFloor` proves

`(1/16) ||lambda||^2 <= ||L_gauge,0^* lambda||^2`.

The selected-background forward defect estimate is converted into an adjoint
estimate by literal finite Cauchy–Schwarz/Frobenius algebra. At
`rho = 1/8192`, the exact coefficient is

`3072 * 16 * (4 rho^2) = 3/1024`.

This retains the selected-background reduced floor

`(29/1024) ||lambda||^2 <= ||L_gauge,A^* lambda||^2`

on componentwise-mean-zero multipliers.

## Orbit-type stratification and a free based computational presentation

`flatConstantRedundancyNotAutomaticallyTransported` gives an exact rational
near-identity noncentral-holonomy counterexample to deleting the three flat
constant modes at every background.

`selectedBackgroundStabilizerNeedNotEqualFlat` and
`nearIdentityStabilizerProfileExact` sharpen this. At the flat identity
holonomy all three pure-quaternion basis coordinates are fixed. For the literal
near-identity x-axis holonomy, x survives while y and z move. Thus the
unbased physical quotient has background-dependent isotropy type.

The new `BalabanBasedGaugeActionFreeExact` proves the complementary
computational fact. On any connected lattice, if a gauge transformation
stabilizes every link and equals the identity at one base site, path covariance
and group cancellation force it to equal the identity at every site. The main
results are

`selectedBasedGaugeStabilizerTrivial`

and

`basedGaugeActionIsotropyTrivial`.

This does not claim that the selected nonlinear variational orbit has already
been shown to meet a based gauge slice. It proves that once a connected based
presentation is used, residual stabilizer isotropy is trivial on that
presentation.

## Concrete flat quotient section

`BalabanSelectedFlatGaugeBasedSectionExact` subtracts each Lie component's
value at `(0,0,0,0)`. It proves that the representative is based, the section
is idempotent, every flat constant-shift class has a unique based
representative, and the actual flat selected gauge transpose is invariant under
this replacement.

`basedSectionNotIdentityOnUnreducedCarrier` exhibits a nonzero constant
multiplier whose based representative is zero. This is the exact finite
section/quotient asymmetry. It remains a flat anchor, not a nonlinear
selected-background gauge-slice theorem.

## Mean decomposition and the first all-carrier floor

`BalabanSelectedGaugeMeanDecompositionExact` proves

`lambda = lambda_0 + P_const lambda`

and

`||lambda||^2 = ||lambda_0||^2 + ||P_const lambda||^2`,

with `lambda_0` componentwise global-mean-zero.

The previous all-carrier theorem then gave

`(29/2048) ||lambda||^2`
`  <= ||L_A^* lambda||^2 + ||P_const lambda||^2`.

`P_const` is a flat reference regularizer. It is not identified with the moving
physical stabilizer.

## New relative-form theorem: `31/64`

`BalabanFiniteRelativeFormPerturbationExact` proves, for arbitrary finite
rational vectors `r,d`, the square-root-free two-sided estimate

`-(1/4 ||r||^2 + 5 ||d||^2)`
`  <= ||r+d||^2 - ||r||^2`
`  <= 1/4 ||r||^2 + 5 ||d||^2`.

Applying this to

`r = L_0^* lambda`,
`d = (L_A^* - L_0^*) lambda`,

and using the exact flat `1/16` floor plus the selected `3/1024` defect yields

`selectedBackgroundGaugePerturbationRelativeFormBound`:

`|q_EA(lambda)| <= (31/64) Q_0(lambda)`

in two-sided ordered form. Therefore

`(33/64) Q_0(lambda) <= Q_A(lambda) <= (95/64) Q_0(lambda)`.

In particular,

`selectedBackgroundRegularizedGaugeFloorThirtyThreeOver1024` proves

`(33/1024) ||lambda||^2 <= Q_A(lambda)`.

This strictly improves the earlier conservative `29/2048` all-carrier floor.
`BalabanSelectedBackgroundGaugeRelativeSmallnessExact` packages the exact
positive complementary slack

`31/64 + 33/64 = 1`.

## Exact flat Green and exact operator decomposition

The flat regularized gauge Gram is the configured componentwise operator
`-Delta_periodic + P_const`. The existing 256-site Fourier kernel is therefore
an exact two-sided Green:

`regularizedFlatGaugeGreenLeftInverse`,
`regularizedFlatGaugeGreenRightInverse`.

With `D_A = L_A-L_0`, the actual selected matrix satisfies

`E_A = L_0 D_A^* + D_A L_0^* + D_A D_A^*`

and

`K_A^reg = K_0^reg + E_A`.

The same `P_const` occurs in both regularized Grams and cancels from their
difference. `regularizedGaugeGramDifferenceOutsideRangeZero` therefore proves
that the perturbation remains local despite the nonlocal regularizer.

## New literal absolute-kernel estimates

The Green problem is no longer only at form level.

`BalabanSelectedFlatGaugeGreenAbsoluteMassExact` evaluates the actual 256-site
Fourier kernel and proves

`sum_x |G_0(x)| = 74077/71680 < 17/16`.

`BalabanSelectedFlatGaugeConstraintAbsoluteMassExact` uses the exact
`L_0^* = -grad_periodic` identification and its two-site stencil to prove

`rowMass(L_0) <= 8`,
`columnMass(L_0) <= 2`.

`BalabanSelectedBackgroundGaugeDefectAbsoluteMassExact` upgrades the selected
squared defect bound to the literal entry estimate

`|D_A(row,column)| <= 1/1024`,

then combines it with the exact two-site-per-direction spatial stencil to give
the conservative but explicit bounds

`rowMass(D_A) <= 3/128`,
`columnMass(D_A) <= 3/512`.

`BalabanSelectedBackgroundGaugeGramPerturbationAbsoluteMassExact` inserts these
constants into the actual three-term perturbation and proves

`rowMass(E_A) <= 6153/65536`.

No abstract perturbation interface is substituted for the physical selected
matrix in this calculation.

## Literal unweighted `G_0 E_A` contraction

`BalabanSelectedBackgroundFlatGreenPerturbationContractionExact` identifies its
matrix `G_0` pointwise with the existing exact componentwise Fourier Green via
`flatGreenKernelActsExactly` and then proves

`rowMass(G_0 E_A)`
`  <= (17/16)(6153/65536)`
`   = 104601/1048576`
`   < 1/10 < 1/2`.

The named endpoint is

`selectedBackgroundFlatGreenPerturbationOneTenthContraction`.

Thus the unweighted Neumann contraction requested by the roadmap is now a
literal finite-kernel theorem on the actual selected carrier, with roughly a
factor-ten margin to one.

## Rational Combes–Thomas weight

`BalabanSelectedBackgroundRationalCombesThomasWeightExact` introduces a
nontrivial periodic radial weight on each `C4` coordinate:

`w : 1, 64/65, (64/65)^2, 64/65`,

with exact inverse

`w^-1 : 1, 65/64, (65/64)^2, 65/64`.

The four-dimensional site weight is the product of the four coordinate
weights. The module proves the pointwise inverse law, `w <= 1`, and the global
side-four bound

`w^-1 <= (9/8)^4 = 6561/4096`.

Diagonal conjugation of the literal residual therefore satisfies

`rowMass(D (G_0 E_A) D^-1)`
`  <= (6561/4096)(104601/1048576)`
`   = 686287161/4294967296`
`   < 1/6 < 1/2`.

The main endpoint is

`selectedBackgroundWeightedGreenPerturbationOneSixthContraction`.

This is an explicit rational weighted contraction on the configured side-four
torus. It is stronger than merely knowing that `E_A` is finite range. It is
not yet a scale-uniform RG estimate: the present global weight-ratio bound uses
the finite side-four diameter.

## What is now genuinely left in the local Green lane

The hard quantitative smallness requested at the start of the tranche is now
closed twice: by the relative-form `31/64` estimate and, more strongly for the
kernel route, by the literal weighted row-mass contraction below `1/6`.

The remaining local Green task is no longer to find a small constant. It is to
turn the finite weighted Neumann parametrices into an honest background inverse
on a complete scalar carrier (or to invoke/prove the finite-dimensional inverse
theorem from the strict all-carrier floor), and then transport the diagonal
weight back to an explicit background Green kernel decay statement.

After that, the still-separate physical geometry is:

- prove that the chosen based/tree gauge is actually a slice of the selected
  nonlinear variational orbit while preserving the selected block-average
  constraint;
- construct the resulting physical tangent projector rather than using the
  flat regularizer as a surrogate;
- prove constrained stationarity / projected Euler–Lagrange for the actual
  minimizer;
- feed the background Green into the literal 15-atom / four-owner producer and
  close the prepared `1/32` Hessian endpoint.

Only then should local finite work stop and the programme pivot to the genuine
four-dimensional bottleneck: scale-uniform RG including large fields,
observable transport, continuum Schwinger functions/OS properties, physical
clustering and gap transfer, nontriviality/asymptotic freedom, and group-scope
uniformization.

## Validation boundary

The cumulative Round-42 root imports every module above. The checker rejects
holes, postulates, unsafe termination/trust escapes, guards the theorem names
and source identifiers, and invokes the pinned Agda 2.9 checker.

No successful Agda-kernel run is claimed until an observable checker/workflow
run completes. Likewise no nonlinear selected-background gauge slice,
background inverse, minimizer theorem, `1/32` physical Hessian closure,
scale-uniform 4D RG theorem, or Clay completion is claimed by this note.
