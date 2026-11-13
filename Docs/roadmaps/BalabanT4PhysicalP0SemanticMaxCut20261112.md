# Bałaban T4 physical P0 — semantic four-orbit max-cut (2026-11-12)

## Source owners

- DASHI/Physics/YangMills/BalabanClayT4LiteralOneLoopBoxEvaluatorExact.agda: actual DiagramExpression, TrigAtom, LiteralScalarIntegrandExpression, BoxTrigEnvironment, RationalIntervalArithmetic, and LiteralGeneratedBoxEvaluator
- BalabanClayT4WilsonOneLoopJointMomentumEquivarianceExact.agda: actual signed-permutation action on atoms and expressions
- BalabanClayT4WilsonOneLoopOrbitEvaluationTransportExact.agda: pre-existing structural expression evaluation covariance
- BalabanClayT4HypercubicOrbitGeometryExact.agda and BalabanClayT4HyperoctahedralGridOrbitExact.agda: pre-existing 256-cell grid, infrared 16, regular orbit sizes 64+96+64+16=240
- BalabanClayT4LiteralEvaluatorFourRepresentativeReductionExact.agda: pre-existing syntax-based conditional orbit transport

## Implemented on this branch (source-written, kernel-unverified)

1. BalabanClayT4LiteralSemanticSevenGeneratorTransportExact.agda:
   ConcreteAtomGeneratorCovariance exhausts the original five TrigAtom forms: sineHalf, cosineFull, hatMomentumSquared, colorCasimir and gaugeParameter. The original sign-sensitive Joint.transformAtom is used throughout. The new seven-generator semantic certificate gives same-box evaluation equalities for the *actual selected* regularIntegrand, not syntactic equality of ASTs. It compiles atom covariance to the original GeneratorEnvironmentCompatibility and transports the source evaluator along the existing generated orbit paths.

2. BalabanClayT4SemanticFourRepresentativeQuadratureExact.agda:
   Extracts four literal CertifiedBoxQuadrature values from the SAME LiteralGeneratedBoxEvaluator and exposes their exact recursive expression values and the 240-cell-to-four-representative evaluator equality. This does not create four numerical quadrature receipts or assume their analytic soundness.

3. BalabanClayT4OuterRankTwoPerAxisExact.agda:
   Proves the exact finite outer-axis tally 2m on the genuine generated box codes. The physical scaled sine-squared denominator inequality is still a separate analytic gate.

4. scripts/check_balaban_t4_semantic_p0_exact.py:
   Supplemental deterministic exact-rational geometry and sign-aware interval-division regression; Agda remains the golden proof authority.

## Corrections to the attached four-gate proposal

- An individual signed coordinate projection is not flip-invariant as a scalar; a sineHalf atom is ODD under a flip. Coordinate covariance must carry the corresponding expression action and environment.
- cos(q_mu-q_nu) becomes cos(q_mu+q_nu) under flipping q_mu; evenness of cosine alone does NOT prove invariance of the original full Wilson/ghost/Haar scalar under individual coordinate flips.
- For numerator [-2,1], strictly positive denominator [2,4], the true interval division hull is [-1,1/2], while the proposed sign-blind formula gives [-1/2,1/2] and is unsound. A verified quotient needs all four corner quotients or a proven numerator sign.
- Four pointwise expression enclosures are not four certified integrals: real quadrature receipts require volume, midpoint/Hessian/error and enclosure soundness on the exact source integrand.
- Full B4 orbit reduction requires joint external-momentum equivariance. If the external momentum stays fixed on axis 0, the source has a conservative seven-class stabilizer route rather than four classes.

## Unpaid physical max-cut

| Gate | Exact remaining lemma or evidence | Status |
| --- | --- | --- |
| P0.0 | Inhabit the genuine LiteralDiagramExpressions, LiteralWardExpressionProofs and LiteralScalarIntegrandExpression with selected physical Wilson, ghost and Haar terms, fixing external momentum convention | OPEN |
| P0.1 | Prove transformed atom intervals for each actual BoxTrigEnvironment, all selected B4 generators | OPEN |
| P0.2 | Prove the seven target-box *semantic* equalities for the exact literal regularIntegrand, not a similarly named proxy | OPEN |
| P0.3 | Prove physical q=pi*x scaling and 4 sin^2(q_mu/2)>=2 on outer coordinate cells; connect the sum to the actual hatMomentumSquared atom and finite rank 2m | OPEN (finite tally source-written) |
| P0.4 | Prove positive denominator and sound sign-aware interval quotient, with numerator bounds on original source | OPEN |
| P0.5 | Construct actual four quadrature/error/volume enclosures and fold into the certified 240-cell integral; use seven classes if axis-fixed | OPEN |
| P0.6 | Local pinned Agda kernel acceptance and first-error repair of the three new source modules | OPEN |

The source search did not find a constructed physical LiteralScalarIntegrandExpression inhabitant; an abstract record signature is not such an inhabitant. This is the highest-information remaining gate. Do not promote P0 or the Yang–Mills E1/D1/D2/N1/G1 physical gates from source-written interfaces.

## Local verification

Run python scripts/check_balaban_t4_semantic_p0_exact.py. Check the three Agda modules with the pinned local Agda 2.9 checker and their transitive imports. CI is not required.

Attribution: original lattice gauge theory source remains with Wilson, Faddeev-Popov, Bałaban and the cited method authors. DASHI owns the new finite semantic proof compilation and four-orbit transport wiring. No new finite orbit theorem substitutes for a physical one-loop integrand or continuum mass-gap proof.


## Adversarial follow-up on the source API

- The exact original flip counterexample, `originalSineHalfFlip0NotSyntacticallyInvariant`, now proves in Agda syntax that the literal sineHalf(loopMomentum,axis0) atom becomes a different constructor (negate rather than atom) under flip0. This does not refute possible full-integrand symmetry; it shows why atom covariance and full-scalar invariance must be different obligations.
- The source TrigAtom grammar has three momentum roles: loopMomentum, externalMomentum and shiftedMomentum. The rank lower bound for the unshifted \\hat{q}^2 is **not** automatically a positive bound for every shifted propagator denominator \\hat{q+p}^2. Each literal denominator appearing in gauge and ghost terms needs its own positivity certificate, and the fixed-axis versus joint external-momentum convention must be tracked.
- A pointwise functional equality under B4 need not imply propositional equality of the two RationalInterval evaluations: interval dependency and expression-tree shape can change enclosures. The new seven-generator record asks for the stronger *evaluated interval equality* at the selected boxes. If a literal expression proves only enclosure inclusion, the correct remedy is a separate sound-inclusion transport using the selected interval backend, not an assumed equality.
- Therefore neither the new semantic certificate TYPE nor the four receipt selectors is evidence that the physical P0 gate is already inhabited. The next highest-information action is constructing the exact literal scalar-source instance and checking which of seven semantic equalities is actually true for its momentum convention, before trying to certify the four quadratures.


## 2026-11-12 cross-PR integration and CMP109 primary-source correction

**Related arithmetic work, separate PR #1479** (branch `chatgpt/epistemic-power-maxcut-20261109`): `BalabanLiteralTotalRationalBackendExact.agda` creates a concrete total `Eval.RationalIntervalArithmetic` with a fixed zero-singleton fallback outside the positive-denominator domain and equality to the original `Typed.divideInterval` on positive inputs. `BalabanLiteralSelectedTotalExpressionTypedDerivationExact.agda` structurally transports full original `Typed.ExpressionInterval` derivations to the selected total evaluator with exact equality at all constructors, consuming real positivity witnesses at quotient nodes. `BalabanLiteralProofIrrelevantIntervalBackendExact.agda` adds full record extensionality and positive-division congruence. **These modules live on the sibling PR and MUST be merged/cherry-picked before importing them here**. Both branches' new Agda proof terms remain kernel-unverified; CI is not required.

**CMP109 source verification:** Bałaban 1987 pages 292–293 equations (5.6), (5.7) establish tensor coordinate/permutation/reflection **covariance with index permutations, orientation signs, and shifted origins**, not unconditional full B4 invariance of an arbitrary scalar `regularIntegrand`. Page 297 equations (5.39)–(5.42) extract beta by a selected tensor coefficient / mixed momentum derivative at zero. Therefore a literal source-specific tensor-to-beta/regular-scalar projection is a necessary independent lemma. An off-diagonal `Π₀₁` component itself changes reflection sign; source eq.(5.7) cannot be directly used as `semanticFlip0` for arbitrary scalar. See `BalabanCMP109TensorCovarianceScalarBoundaryExact.agda` on sibling PR #1479. Primary PDF: https://scispace.com/pdf/renormalization-group-approach-to-lattice-gauge-field-3ygai0vxt1.pdf.

**Existing Bishop denominator owner, previously omitted from this ledger:** `BalabanBishopOuterBrillouinSineGapExact.agda`, `BalabanBishopMachinNormalizedOuterMomentumExact.agda`, `BalabanWilsonFourierMachinPeriodCarrierExact.agda`, `BalabanClayT4MachinOuterSineToCanonicalGapExact.agda` and `BalabanClayT4BishopRegularHatMomentumGapExact.agda` already provide a constructive **conditional** physical lower-bound path with the explicit rational component gap `7569/4096 > 0`. This is not equal to the sharper unproved per-axis `2` bound: `2 - 7569/4096 = 623/4096`. Neither the per-box same-object sine/Machin coordinate weld nor positivity of the computed rational interval lower endpoint follows from pointwise Bishop positivity alone.

**Quadratures:** source-owned 4,6,4,1 weights and conditional selection of four existing `CertifiedBoxQuadrature` receipts do NOT provide four numerical values or error certificates. The underlying original four-diagram `LiteralDiagramExpressions` / `LiteralScalarIntegrandExpression` inhabitants, every shifted-propagator positivity proof, and actual `CertifiedBoxQuadrature` input proofs remain **OPEN**. Do not use `⊤` to inhabit the analytic `Set` fields or fabricate four scalar integrals.

**Physical max-cut after this audit:** (1) actual Wilson/ghost/Haar + Ward tensor-to-scalar source instance; (2) source-correct transformed generator laws of that projected scalar (possibly only fixed-axis six), (3) original Fourier-coordinate/Machin materialisation and strict positive rational intervals at every unshifted/shifted denominator, (4) four true recursively generated quadrature outputs and rigorous errors. Local kernel acceptance of all new Agda proofs is distinct and still unverified.


## 2026-11-12 continued actual proof max-cut — checked source vs physical admission

**New source-written Agda on PR #1479:**
- `BalabanLiteralRecursivePositiveDivisionCompilerExact.agda` implements `AllDivisionsPositive` over the ORIGINAL `Eval.DiagramExpression`. `checkAllDivisionsPositive` is a computable `Dec` over every nested AST denominator, using the **selected original evaluator's rational lower endpoint** and `ℚP._<?_`; `compilePositiveDerivation` produces the ORIGINAL `Typed.ExpressionInterval` derivation when positive; `positiveFromTypedDerivation` proves the converse from any original typed derivation, and `decideSelectedTypedDerivation` returns either the exact derivation or a constructive refutation. This eliminates handmade *per-expression* typed derivation inputs.
- `BalabanLiteralBishopPositiveExpressionCompilerExact.agda` proves compositional canonical Bishop semantics for that same AST from actual `Canonical.PhysicalTrigBoxData`, atom-interval equality to the selected `Eval.BoxTrigEnvironment`, and `AllDivisionsPositive`. It applies existing genuine `Sem.divideCertificate` at each positive quotient and establishes full rational interval equality with the selected recursive evaluator.
- `BalabanLiteralRecursiveDivisionPositiveNegativeControlExact.agda` proves literal rational expression 1/1 has a typed positivity derivation, while 1/0 cannot inhabit `AllDivisionsPositive`. The total backend zero fallback is **not** source-positive division.
- `scripts/check_balaban_p0_arithmetic_local.sh`: pinned local Agda import-order check of 17 new source modules, no CI. No Agda binary was present in this execution environment, so none of the new files has a kernel acceptance receipt.

**New source-written Agda on sibling PR #1498:**
- `BalabanClayT4OriginalEvaluatorFourOrbitEndpointSumsExact.agda`: from the SAME actual `LiteralGeneratedBoxEvaluator` and `LiteralSevenSemanticGeneratorData` supplied by the source, proves `normalizedRegularSum(sourceLower/sourceUpper) ≡ fourOrbitNormalizedValue(sourceLower/sourceUpper)` with original 4,6,4,1 weights. The lower/upper per-cell rationals are projected directly from `Eval.regularIntegrandEvaluation` and `Eval.intervalValueExact`, not independent four numbers.
- `BalabanClayT4LiteralFourOrbitErrorBudgetFoldExact.agda`: computes candidate weighted error budget from the **four actual** `Eval.quadrature` error fields and folds it with exact normalized lower/upper endpoints. A further theorem covers the genuine full 240-cell error sum **ONLY** when the original error function itself has an independent `CMP109ScalarEuclideanSymmetry` witness. Semantic invariance of integrand endpoint values alone does **not** prove error covariance, quadrature rule compatibility, or physical integration error validity. This is a new exact source-dependent CUT, not an assumed theorem.
- Updated sibling no-CI checker to include both new modules.

**Primary physical owner check:** `BalabanClayT4WilsonOneLoopConventionExact.agda` selects canonical SU2/gauge/Haar/Fourier conventions and coefficient `11/24` but contains **no formulas** inhabiting `LiteralDiagramExpressions` with four Wilson bubble/tadpole/ghost/Haar numerator-denominator pairs or the corresponding Ward tensor-to-scalar reduction. Those source formulas, tensor covariance through beta extraction, actual trig atom enclosures including SHIFTED momenta, strictly positive lower endpoints on each real denominator node, four numerical quadrature values and their Hessian/integration proofs remain **OPEN**. In particular the original rank-one box contains zero in three inner coordinates, so no product of individually inverted sine-square terms is positive there; source must use the genuine summed propagator or another justified kernel.

**Verification:** GitHub source written/readback, no local Agda, no CI, no status promotion. Python exact sanity: 256 grid cells = 16 inner + 64/96/64/16 regular; rational 1>0 versus 0≯0, signed four-corner rational division behaves correctly. These checks do not constitute physical or kernel proof.


## 2026-11-12 source-contract repair and refined original Wilson denominator

**New high-information discovery:** Original `LiteralScalarIntegrandExpression` demanded two incompatible *syntax equalities* `scalarIntegrand ≡ divide numerator denominator` and `scalarIntegrand ≡ add continuumSingular regularIntegrand`. Since the two constructors of the original free `DiagramExpression` are disjoint, there was provably NO possible source instance, independent of any physics. `BalabanClayT4LiteralScalarSyntaxContradictionExact.agda` retains an unconditional constructor-disjointness negative control. The canonical `BalabanClayT4LiteralOneLoopBoxEvaluatorExact.agda` now replaces the impossible second field with a point-indexed **source scalar interpretation** via `LiteralScalarPointSemantics`/`interpretScalarAt`, requiring a semantic setoid equation `singularRegularSplitExact` at each selected point. This fixes the syntax contradiction but DOES NOT create the actual Wilson/ghost/Haar physical interpretation or prove its faithfulness to the Bishop/Fourier/diagrammatic source. Do not promote this record alone as physical completion.

**Actual refined square and 240-source-cell positivity:** `BalabanClayT4RefinedSineSquareRegularBoxesExact.agda` defines `refinedSquare` with lower = max(0, original four-corner lower) and upper = original four-corner upper; proves its soundness for the **same Bishop real squared twice** using `BishopP.nonNegSquare`. The selected coarse sine windows for negativeOuter, negativeInner, positiveInner, positiveOuter are [-1,-87/128],[-1,1],[-1,1],[87/128,1] respectively. Only the per-cell TRUE physical membership of the original sine-half atom remains to be produced by the existing Machin sine/normalization owners. `sourceRegularWilsonLower` proves (by the actual original 256-cell source grid) that every one of the 240 regular unshifted Wilson summed denominators has exact rational interval lower >= **7569/4096**; the 16 infrared boxes are excluded by contradiction. `sourceStrictPositiveAtRegularBox` exports a typed rational positivity proof. This is strictly weaker than the unproved rank 2m bound.

**Source-real Bishop-value weld:** `BalabanClayT4RefinedOriginalWilsonBishopEnvironmentExact.agda` takes four explicit `ActualSourceFourSineMembership` proofs about the SAME canonical Bishop sine-half atoms and constructs `originalWilsonHatSound`, a physically meaningful `BishopLiesIn` certificate for the original unshifted Wilson `hatMomentumSquared` in the refined positive rational box. `refinedLoopBishopEnvironment` improves exactly the loop-momentum atom while preserving canonical external and shifted momentum atoms untouched. The four *physical* sine memberships, the shifted momentum domains and actual division nodes remain OPEN; this is not an unrestricted square assumption.

**Seven genuine original-generator denominator invariances:** `BalabanClayT4RefinedWilsonSevenGeneratorExact.agda` proves exact source rank formula for BOTH interval endpoints of the same refined unshifted Wilson denominator over all original 256 boxes, then imports `Action.outerCountGeneratorInvariant` to derive `sourceWilsonGeneratorLowerExact` and `sourceWilsonGeneratorUpperExact` for all seven actual B4 generators. It does NOT prove seven symmetries of the Wilson BUBBLE + ghost + tadpole + Haar **regular scalar**; that still requires the actual source tensor-to-beta extraction and transformed shifted propagators.

**Adversarial normal-form control:** `BalabanClayT4NaiveNormalizedSineSquareCounterexampleExact.agda` shows original generic four-corner multiplication sends the inner sine interval [-1,1] squared to [-1,1], and a rank-one 3-inner/1-outer source Wilson denominator fails a positive interval lower test, despite the corrected dependency-aware box admitting it. Any `DiagramTrigNormalForm.normalizeHatMomentum` rewrite into naïve products must therefore use a refined square evaluator or transport proof before positive-division admission.

**FOUR EXPLICIT AUXILIARY RATIONAL ENCLOSURES, NOT BETA INTEGRALS:** `BalabanClayT4FourAuxiliaryWilsonPropagatorBoxesExact.agda` computes the true original `Typed.divideInterval` on four original source representatives for 1 / unshifted Wilson hat-momentum², giving rank m=1..4:
- r1: [1/16,4096/7569]
- r2: [1/16,2048/7569]
- r3: [1/16,4096/22707]
- r4: [1/16,1024/7569]
The geometric 4,6,4,1 weighted direct interval envelope is **[15/16,105472/22707]**, conditioned on uniform physical sine membership over each source cell. This is a coarse bound of the *free propagator*, **not** values/errors for the source's Wilson+ghost+Haar vacuum polarisation tensor or four beta-integrand quadratures. No physical error certificate or original beta-integral numerical value is claimed.

**Independent rational regression:** `scripts/check_balaban_t4_refined_wilson_exact.py` covers all 256 cells, 240 regular/16 infrared, all 1792 original seven-generator image comparisons, the sign-sensitive interval arithmetic and exact four auxiliary representative bounds. Executed independent Python `Fraction` check: PASS. Static GitHub readbacks show no obvious holes/postulates. **No Agda kernel available** on this runtime, no CI. Local checker `scripts/check_balaban_t4_semantic_p0_local.sh` now checks eleven Agda modules.

### Still-unpaid physical terminal cut (do NOT promote)

1. **LIT:** actual four Wilson/ghost/Haar momentum-dependent kernel numerator/denominator ASTs, Ward cancellations, tensor-to-beta and actual canonical Bishop-point `LiteralScalarPointSemantics` with no `⊤` semantic shortcuts.
2. **SYM:** seven literal scalar B4 semantic equalities (or source-correct fixed external-axis six), including the shifted momentum sine/cosine action and original tensor reflection signs; current proof is for unshifted denominator only.
3. **TRIG:** prove actual four physical `ActualSourceFourSineMembership` propositions on every original box using Machin `q=πx` and constructive sine bounds; separately prove each shifted propagator denominator positive in the ORIGINAL selected AST, not merely the unshifted one.
4. **QUAD:** instantiate source `LiteralGeneratedBoxEvaluator` and all four actual `CertifiedBoxQuadrature` with source-evaluated scalar intervals, true midpoints, Hessian/error inequalities, integral enclosures, and separately transported error covariance. Four proxy free-propagator intervals do not discharge QUAD.
5. **KERNEL:** local pinned Agda checking / first type-error repair for all new modules; no CI.

**No physical Clay E1/D1/D2/N1/G1 terminal result follows.**


## 2026-11-13 source-accurate P0 maximum cut (from attached 12-group proposed resolution)

The authoritative detailed declaration-by-declaration audit is in
`Docs/roadmaps/BalabanP0MaxCutAttachmentAudit20261113.md`.
The attachment's blanket "12/12 constructively closed" claim is NOT
accepted as a local Agda or physical source receipt. The real Wilson
Hessian, reduced FP jet, Haar Casimir and mixed derivative beta extractor
already exist and are REUSED; the same-source finite Fourier/determinant,
quartic analytic remainder, Ward tensor-to-scalar and real quadrature
certificates still do not follow from those independent leaves.

New source-written exact modules (PR #1498):
- `BalabanP0FreeGhostWilsonPositiveWeldExact.agda`: source free ghost
  Fourier symbol and original Wilson hat momentum live in the SAME
  positive Bishop/rational box given true source four-sine membership.
  Crucially `derivedCoherentGhostFromOriginalSine` constructs the
  coherent ghost box directly from the existing sine-derived cosine owner.
- The source `BalabanClayT4FaddeevPopovWilsonSymbolBridgeExact.agda`
  is now SETOID-correct: half-angle and sum transport are `Bishop._≃_`
  rather than unprovably strict `_≡_` of Cauchy records.
- `BalabanP0TransverseGaugeFixingNoGoExact.agda`: proves exact algebraic
  gauge-fixed Laplacian identity and counterexample to Wilson `d*d=Δ`;
  source SU2 rational normalisation `(11/3)C_A/16 = 11/24`,
  with `C_A=2`, not the attachment's `2N=4`.
- `BalabanP0SU2HaarQuarticFormalJetExact.agda`: formal SU2 Haar
  `log J` quartic term is `-r⁴/1440`, and -log J has positive
  quadratic/quartic terms. The analytic remainder is NOT paid.
- `BalabanP0FourOrbitMidpointHessianBudgetAlgebraExact.agda`:
  original-cell x-domain midpoint coefficient M2/384; Brillouin
  physical-measure coefficient M2/6144; exact orbit budget
  (4 M1+6 M2+4 M3+M4)/384. The true source Hessian bounds and integral
  inclusions are STILL missing.
- Corrected original `Eval.rationalInterval` compatibility alias
  for already-imported Bishop reciprocal/semantics modules.
- The existing local no-CI checker now enumerates 18 source modules.
  Static GitHub readback plus independent exact Fraction/SymPy rational
  checks PASS. No Agda executable was available; new Agda declarations
  remain kernel UNVERIFIED.

P0.1–P0.12 exact remaining theorem owners and dependency order are in
the new audit. Critical unpaid physical frontier:
(1) original P33 Wilson 3/4-momentum vertex and FP/Haar SAME-source
chart/determinant/analytic remainder;
(2) instantiate `LiteralDiagramExpressions`, actual Ward and off-diagonal
second jet / singular-regular semantics;
(3) real Machin/Fourier cell sine memberships for loop AND shifted roles,
actual seven scalar symmetries or correct stabilizer;
(4) FOUR TRUE `CertifiedBoxQuadrature` values, Hessian error proofs and
error covariance; (5) real Bałaban coefficient and quartic RG remainder.
One-loop beta sign/algebra alone does not prove Clay E1/D1/D2.


## 13 November 2026 — attached second max-cut execution: new source-written results

**Controlling machine-readable ledger:** `Docs/roadmaps/BalabanP0ExactRemaining20261113.json` (12 exact P0 gates, source lemma owners, highest-information next actions, and independent source/kernel/physical statuses).

The 2026-11-13 attachment contains further proposed mathematical calculations, NOT repository-ready proofs of the four physical one-loop integrals or a local Agda acceptance receipt. Among its formulas, `4*(7071/10000)^2 = 199996164/100000000` (not 199995284/100000000), and the physical Fourier measure requires an **additional 1/16** beyond the x-chart cell volume in the four-orbit integral, as proved previously by `BalabanClayT4AuxiliaryWilsonNormalizedMeasureExact`. The proposed `I_total = 11 log 2/(24 pi²) ± E` lacks actual source-generated quadrature numbers and a proved Hessian/error bound. The suggested uniform Haar sixth-order and reduced FP Bishop-path fifth-order analytic remainders remain unproved, regardless of correct formal Taylor coefficients.

**P0.4 structural physical source topology PAID CONDITIONALLY:** `BalabanP0LiteralDiagramTopologyFromSourceExact.agda` constructs an actual `Eval.LiteralDiagramExpressions` from source-owned numerator ASTs, with true original denominator topology: gauge bubble and signed FP ghost each divide by `hat(p)^2 * hat(p+k)^2`, tadpole by `hat(p)^2`, and local Haar insertion by `1`. All four quotient-definition equalities and common ghost/bubble denominator equality hold by `refl`. The Lorentz/color-indexed physical numerators are **not** invented; their construction from P33 3/4 jets and ghost/Haar sources is the remaining original physical owner.

**P0.5 actual tensor-index carrier source-written:** `BalabanP0LiteralIndexedTensorWardSourceExact.agda` materializes the four diagram ASTs at every `(mu,nu)` from source-owned indexed numerators and the correct four-axis original lattice derivative. Its `fourAxisContraction` is an honest sum `Σ_mu D_mu Pi_{mu,nu}`, not the invalid choice `longitudinalContract = λ _ _ → constant 0`. The actual Fourier derivative phase, distributivity *under a sound semantic interpreter*, and source-specific Ward defect cancellation remain **OPEN**.

**P0.6 original CMP109 off-diagonal beta join PAID CONDITIONALLY:** `BalabanP0FourOriginalDiagramMixedTwoJetWeldExact.agda` assembles the four source `OffDiagonalTwoJet` objects and proves that their mixed coefficient is the actual four-term sum. `fourOriginalDiagramJetsExtractBeta` consumes the **same source** jet identification and the original `CMP.cmp109MixedDerivativeExtractsBeta` theorem to extract beta with the correct negative sign. The real Wilson/FP/Haar indexed jet equality and third-order remainder proof remain OPEN. *Beta is not the mixed derivative of a constant `Pi_scalar`; it is extracted from the off-diagonal component of the tensor.*

**P0.1 FREE gauge inverse PAID CONDITIONAL ON STRICT POSITIVITY:** `BalabanP0FeynmanGaugeRationalPropagatorInverseExact.agda` proves all 16 indexed components of the actual rational matrix identity `(s δ)*(δ/s)=δ` using the existing `positiveReciprocalRightInverse`, and rejects s=0. This is the source-compatible free Feynman-gauge inverse, not a higher Wilson vertex or the finite-background propagator.

**P0.2 physical reduced ghost finite logarithmic remainder now REUSED AND JOINED:** A broader repository search uncovered existing `BalabanReducedGhostPhysicalMatrixLogFifthTailExact`, `BalabanReducedGhostSignedMatrixLogTailExact`, `BalabanReducedGhostMatrixLogShiftedTailExact`, and `BalabanReducedGhostSignedTraceTailExact`. Their exact same physical *anchored* reduced FP matrix already has row contraction below 1/5, signed degree-five tail cap <= **1/2500**, shifted decay `(1/5)^m/2500` and literal finite trace recursion. `BalabanP0PhysicalReducedGhostFiniteLogTailWeldExact.agda` produces signed and shifted certificates simultaneously on the same matrix, and a source-specific trace one-step equality. What remains OPEN is the Bishop background path vs rational jet O(g^5), principal matrix log det identification, and the original 4D Fourier momentum loop/source tensor.

**P0.5 no-go and physics boundary:** `BalabanP0TransverseTensorNotAutomaticallyScalarProjectorExact.agda` has a concrete 4D rational even transverse tensor `T(k)=P(k) diag(k_i²) P(k)` with `P(k)=||k||² I-k kᵀ`. At k=(1,2,0,0), `T00=32,T22=0,P00=4,P22=5`: no scalar multiple P can equal T. The finite algebra proves Ward transversality; Python `Fraction` regression additionally checks simultaneous hyperoctahedral covariance over all 384 signed permutations at k=(1,2,3,4). Thus exact all-k single-projector factorization is NOT a consequence of Ward and B4 alone; CMP109 correctly uses only the *quadratic off-diagonal two-jet* plus higher-order remainder.

**Source/run receipts:** `scripts/check_balaban_p0_attachment_maxcut_exact.py` is the independent Fraction regression for the corrected sine-square rational, 11/24 SU2 coefficient, Haar logarithmic fourth jet, physical volume, midpoint/Hessian and physical ghost fifth-tail, plus 384 signed-axis tensor covariance tests. The no-CI `scripts/check_balaban_t4_semantic_p0_local.sh` now includes **24 target Agda modules**. Local Python Fraction equivalents were executed and passed. No local Agda or Nix was available in this runtime; all this round's new Agda declarations are source-written but **not kernel accepted**.

**Remaining physical highest-information cut:** (i) actual indexed P33 Wilson cubic/quartic Fourier vertices, reduced FP log det and Haar chart; (ii) source-specific indexed bubble/tadpole/FP/Haar numerator ASTs, Ward semantic cancellation and CMP109 off-diagonal two-jet including remainder; (iii) true same-Fourier sine and shifted denominator proofs; (iv) actual scalar-source B4 or stabilizer invariance; (v) four TRUE integral values, Hessian/integration error proofs with source error covariance; (vi) Bałaban coefficient and RG quartic remainder matching. These are not reducible to already paid free-symbol, finite tail or rational normalization arithmetic, and none justifies Clay E1/D1/D2 physical promotion.


## Cross-lane source audit (2026-11-13): original Wilson M.02/F19 PR #1444 is NOT the Bałaban P0 scalar

PR #1444's authoritative original native 1,024-bond interacting
Wilson Gibbs chain now contains:
- original canonical 1,024-bond -> physically sorted 64 ordered pairs
  + 896 spectators reindex, retaining the full interacting weight;
- `originalFinePhysicalPartitionEqualsActualEffectivePartition` from
  the original source F19 finite Haar fibre;
- original physical two-marked normalized source with the SAME
  canonical original Wilson partition;
- new `YMClayOriginalWilsonCanonicalMarkedReindexExact` for
  *arbitrary* marked original canonical observables under the native
  adjacent-swap programme;
- new 64-pair/896-spectator two-sided codec and
  `YMClayOriginalWilsonCanonicalBlockedMarkF19Exact`, a
  source-written direct **all coarse-block-observable** original
  fine-to-physical-effective numerator/normalized pushforward;
- new `YMClayOriginalWilsonEffectiveBetaFiniteDifferenceExact`:
  source partition equality transports exact finite first/second
  differences in Wilson coupling beta (this is **NOT** the original
  CMP109 mixed external-momentum tensor beta coefficient);
- strict positive equal-partition countercontrol shows nonconstant
  normalized original F,G,FG moments can retain a nonzero 1/4
  discrepancy between *effective* and *bare* measures for every
  cutoff. Thus partition pushforward does **not** entail P0.F
  UV-uniform RG decay.

These results are source-written on PR #1444, **local Agda kernel
PENDING**. The original SU(N) matrix/trace authority, scalar carrier
identification, and true P0.F decay estimate remain OPEN.

**Physical interface firewall:** a finite exact 1,024-link Wilson Haar
Gibbs pushforward does not identify the momentum-dependent
Wilson + Faddeev–Popov ghost + Haar fourth-order background perturbative
vacuum-polarization kernel. PR #1498 still requires genuine
`ActualPhysicalDiagramNumeratorSources` for the four indexed ASTs,
source Ward cancellation and CMP109 off-diagonal two-jet, true Fourier
sin/cos membership (especially shifted propagator denominators),
seven actual combined-scalar symmetry identities, four physically
evaluated integrals and Hessian error receipts, and source quartic
remainder. No spectral-gap or Clay claim follows from either finite
partition equality or one-loop beta arithmetic.
