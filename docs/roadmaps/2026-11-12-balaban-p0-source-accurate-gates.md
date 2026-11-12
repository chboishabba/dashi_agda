# Bałaban CMP109 / physical P0 — source-accurate max-cut (2026-11-12)

**Primary source:** T. Bałaban, *Renormalization Group Approach to Lattice Gauge Field Theories. I*, Commun. Math. Phys. **109** (1987), 249–301, DOI 10.1007/BF01215223; source PDF https://scispace.com/pdf/renormalization-group-approach-to-lattice-gauge-field-3ygai0vxt1.pdf.

**Source admissibility and attribution:**
- Page 292, Eq. (5.6): coordinate-permutation **tensor** covariance of the vacuum-polarisation kernel `Π_{μν}`.
- Page 293, Eq. (5.7): coordinate-reflection tensor covariance with orientation factors `ε_μ ε_ν` and shifted lattice bond origins; (5.12)–(5.13) transport the corresponding momentum tensor and include phases.
- Page 297, Eqs. (5.39)–(5.42): beta is extracted from a selected coefficient / the negative mixed derivative at zero momentum (equivalently a second spatial moment) of the vacuum-polarisation tensor, rather than from an arbitrary invariant scalar function of momentum.
- Hence **full B4 invariance of a freely chosen `LiteralScalarIntegrandExpression.regularIntegrand` does not follow directly from CMP109 (5.6)/(5.7)**. A same-source tensor-to-beta/regular-scalar reduction and its differentiated / integrated covariance are mandatory. `BalabanCMP109TensorCovarianceScalarBoundaryExact.agda` is a source-indexed sign countercontrol. The original `BalabanCMP109VacuumPolarizationHypercubicSourceSymmetryExact.agda` explicitly asks for post-projection scalar invariance and should continue to do so.

## Gate A — selected total arithmetic backend

Source-written implementations:
- `BalabanLiteralProofIrrelevantIntervalBackendExact.agda`: full record equality and operation congruences, including two-sided positive-division; `ℚP.≤-irrelevant` / `ℚP.<-irrelevant` from standard Agda rational properties.
- `BalabanLiteralTotalRationalBackendExact.agda`: concrete `Eval.RationalIntervalArithmetic`, exact `Typed` operations for constants/add/subtract/multiply/negate and an explicitly total `totalDivide` extension of `Typed.divideInterval` (fallback `[0,0]` when denominator lower is NOT positive). Proves actual soundness propositions under **strict denominator positivity** and all `EndpointStableBackend` congruences. No claim of meaningful quotient values outside the domain.
- `BalabanLiteralSelectedTotalExpressionTypedDerivationExact.agda`: *structural induction on the original* `Typed.ExpressionInterval` derivation, showing `Eval.evaluateExpression selectedArithmetic` equals the original proof-indexed interval on every valid expression. The quotient case consumes the original positive-denominator witness.
- These source-written declarations are NOT Agda-kernel-accepted here: no executable Agda or Nix environment is present. **Status: conditional source-written closure for the positive domain, kernel UNVERIFIED.**

## Gate B — seven literal physical source symmetries

Existing `BalabanLiteralSevenGeneratorScalarAtomCertificatesExact.agda` proves the seven syntactic laws on source-native scalar atoms and compositional constructors. It does NOT inhabit `LiteralRegularIntegrandB4GeneratorCertificate scalar` for actual Wilson/ghost/Haar diagrams. Source CMP109 tensor covariance has nontrivial reflected off-diagonal signs and bond shifts; a true invariant scalar requires source-specific contraction/ward extraction and transformed trigonometric atoms. **OPEN.** A fixed external momentum axis might require the existing 240→7 stabilizer partition instead of full 240→4.

## Gate C — physical denominator enclosures

Do not discard already implemented Bishop proof owners:
- `BalabanBishopOuterBrillouinSineGapExact.agda`: constructive outer-angle floor `(2 sin t)^2 ≥ 7569/4096` on the admitted angle window `3/4 ≤ t ≤ 11/7`.
- `BalabanBishopMachinNormalizedOuterMomentumExact.agda`: derives that window from Machin `π` and normalized outer coordinate, given a selected `MachinNormalizedOuterCoordinateData`.
- `BalabanWilsonFourierMachinPeriodCarrierExact.agda`: one canonical Machin period carrier; the literal Fourier evaluator has not been demonstrated to consume it.
- `BalabanClayT4MachinOuterSineToCanonicalGapExact.agda` and `BalabanClayT4BishopRegularHatMomentumGapExact.agda`: selected same-object `MachinOuterSineCanonicalWeld` yields positive 4D Wilson denominator at a point, **conditional on the actual per-box coordinate and sine-object identification**.
- `BalabanLiteralOriginalGridDenominatorMaskExact.agda`: 240 source-grid rational rank inequality and denominator admission; its hypothetical `2m` lower intervals require *stronger per-axis certificates* than the existing coarse `7569/4096` theorem. Never substitute one bound for the other.
- **OPEN:** materialise the actual normalised Fourier-coordinate and sine atom over each source box, produce *positive lower endpoints for the selected rational interval denominator* (not just pointwise Bishop positivity), and weld that denominator AST into all divided Wilson/ghost/Haar terms.

## Gate D — four physically certified quadratures

- `BalabanClayT4HypercubicOrbitQuadratureWeightsExact.agda` proves *geometric* weights 4,6,4,1.
- `BalabanCMP109FourOrbitNormalizedQuadratureExact.agda` conditionally proves weighted assembly for a source-symmetry invariant contribution.
- `BalabanCompactHaarFiniteQuadratureErrorExact.agda` proves finite error summation only when cell oscillation and discrepancy proof inputs are supplied.
- `Eval.CertifiedBoxQuadrature` stores `midpointInsideInterval : Set`, `hessianBoundValid : Set`, `quadratureErrorFormulaValid : Set`, `trueIntegralInsideIntervalPlusError : Set`. Declaring or filling these with `⊤` is NOT a physical proof receipt.
- No actual four source `regularIntegrand` / `CertifiedBoxQuadrature` instances, evaluated intervals, or verified numerical errors were found. **OPEN**. Source eq. (5.42) specifies a tensor mixed derivative/moment, not an automatically identified integral of the proposed source AST: validate the matching analytic formula before numerics.

## Strict next source-writing target

1. Instantiate `Eval.LiteralDiagramExpressions` with the **actual** Wilson bubble, tadpole, FP ghost, and Haar kernels and `LiteralScalarIntegrandExpression` with an actual tensor-to-beta/regular-scalar normalisation. No invented constants or proxy expressions.
2. Prove source (5.6)/(5.7) transformed bond/index/phase covariance on that instantiated source and the scalar projection; determine whether 240→4 or the fixed-axis 240→7 reduction applies.
3. Link actual Fourier box coordinates and canonical Machin sine atom enclosures to a positive lower-endpoint `Typed` denominator at every division node. Compose `selectedTotalRecursionIdentifiesTypedDerivation`.
4. Produce the actual four recursive expression interval evaluations and a certified direct-integration / midpoint-Hessian remainder, with numerical source replay receipts and outwards-rational endpoints; then consume the exact geometric weights.

**Verification:** New files committed/read back; source-written proofs are NOT marked Agda-kernel accepted and all source-dependent analytic and physical gates are OPEN. User requested no CI.
