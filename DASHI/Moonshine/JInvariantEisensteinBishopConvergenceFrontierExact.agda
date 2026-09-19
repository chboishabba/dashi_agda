module DASHI.Moonshine.JInvariantEisensteinBishopConvergenceFrontierExact where

------------------------------------------------------------------------
-- EISENSTEIN q-SERIES: EXACT BISHOP / SAME-CARRIER CONVERGENCE FRONTIER
--
-- DASHI CONTRIBUTION / REPO CROSS-POLLINATION
--
-- This owner sharpens the old blanket
--
--   finite truncation -> infinite analytic Eisenstein series
--
-- debt by reusing the convergence and q-decay machinery already checked or
-- source-written in this repository.
--
-- Two convergence routes are kept distinct rather than conflated:
--
--   A. Bishop setoid route
--      vendored Bishop SeriesOf + absolute convergence + componentwise complex
--      limits.  Its remaining application seam is still a weld to the older
--      propositional-equality `ConcreteComplex` evaluator.
--
--   B. same-ConcreteComplex route
--      the literal finite E4/E6 truncation sequences are already compiled to
--      same-carrier limits from explicit componentwise Cauchy evidence.  This
--      route avoids the Bishop carrier weld, but still needs the quantitative
--      Cauchy/majorant proof.
--
-- Since the previous frontier, the finite coefficient side is also sharper:
--
--   sigma_3(n) <= n^4,
--   sigma_5(n) <= n^6
--
-- are owned on the internal divisor kernel.  The literal q producer now has a
-- principal-strip modulus compiler and an upper-half-plane decay compiler:
-- given explicit nondegenerate order/branch evidence,
--
--   Im(tau)>0 -> |q(tau)|<1.
--
-- The generic compiler is paid; inhabiting those order/branch inputs on a
-- selected ordinary analytic package is not silently inferred from the bare
-- ConstructedOrderedCompleteReal interface.
--
-- SOURCE / CODE ATTRIBUTION
-- Errett Bishop and Douglas Bridges, Constructive Analysis, Springer, 1985,
-- DOI 10.1007/978-3-642-61667-9.
-- Zachary Murray, "Constructive Analysis in the Agda Proof Assistant",
-- Dalhousie University BSc Honours thesis, 2022, arXiv:2205.08354; no DOI.
-- Viktor Csimma's continuation is pinned by DASHI at vendor/bishop commit
-- 240e38c7f6938f20f865b1f956c5f084da48bd54.
--
-- The decomposition and adapters below are DASHI contributions. Citations do
-- not import proof authority by themselves.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import Real as BishopReal
import RealProperties as BishopProperties
import Sequence as BishopSequence

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as BishopComplex
import DASHI.Analysis.BishopPolynomialGeometricSeriesConvergenceExact as PolyGeo
import DASHI.Foundations.BishopConstructiveRealBridgeExact as Bishop
import DASHI.Foundations.BishopFinSumSeriesBridgeExact as FinSum
import DASHI.Mathematics.NumberTheory.FiniteDivisorPowerSumBoundExact as PowerBound
import DASHI.Moonshine.JInvariantEisensteinSameCarrierLimitCompilerExact as SameCarrier
import DASHI.Moonshine.JInvariantEisensteinTruncationIncrementExact as Increment
import DASHI.Moonshine.JInvariantEisensteinIncrementCoefficientBoundExact as IncrementBound
import DASHI.Moonshine.JInvariantQPrincipalStripModulusExact as QModulus
import DASHI.Moonshine.JInvariantQUpperHalfPlaneDecayCompilerExact as QDecay

------------------------------------------------------------------------
-- Canonical aliases to the already-owned checked Bishop convergence engine.
------------------------------------------------------------------------

bishopSeriesLimit :
  (terms : Nat -> BishopReal.ℝ) ->
  Bishop.BishopAbsoluteSeriesConvergent terms ->
  BishopReal.ℝ
bishopSeriesLimit = Bishop.bishopSeriesLimit

bishopSeriesLimitConvergence :
  (terms : Nat -> BishopReal.ℝ) ->
  (absolute : Bishop.BishopAbsoluteSeriesConvergent terms) ->
  Bishop.BishopConvergesTo
    (BishopSequence.SeriesOf terms)
    (bishopSeriesLimit terms absolute)
bishopSeriesLimitConvergence = Bishop.bishopSeriesLimitConvergence

finitePrefixMatchesBishopSeries :
  (terms : Nat -> BishopReal.ℝ) ->
  (count : Nat) ->
  BishopReal._≃_
    (FinSum.finSum terms count)
    (BishopSequence.SeriesOf terms count)
finitePrefixMatchesBishopSeries = FinSum.finSumIsSeriesOf

record BishopAbsoluteSeriesLimitReceipt
    (terms : Nat -> BishopReal.ℝ) : Set where
  constructor bishop-absolute-series-limit-receipt
  field
    absoluteConvergence : Bishop.BishopAbsoluteSeriesConvergent terms
    limit : BishopReal.ℝ
    canonicalLimit : BishopReal._≃_ limit (bishopSeriesLimit terms absoluteConvergence)
    convergesToLimit :
      Bishop.BishopConvergesTo (BishopSequence.SeriesOf terms) limit

open BishopAbsoluteSeriesLimitReceipt public

compileAbsoluteSeriesLimit :
  (terms : Nat -> BishopReal.ℝ) ->
  (absolute : Bishop.BishopAbsoluteSeriesConvergent terms) ->
  BishopAbsoluteSeriesLimitReceipt terms
compileAbsoluteSeriesLimit terms absolute =
  bishop-absolute-series-limit-receipt
    absolute
    (bishopSeriesLimit terms absolute)
    BishopProperties.≃-refl
    (bishopSeriesLimitConvergence terms absolute)

compileComponentwiseComplexLimit :
  (terms : Nat -> BishopComplex.BishopComplex) ->
  (absolute : BishopComplex.ComponentwiseAbsoluteSeriesConvergent terms) ->
  BishopComplex.ComplexSeriesConvergesTo
    terms
    (BishopComplex.complexSeriesLimit terms absolute)
compileComponentwiseComplexLimit = BishopComplex.complexSeriesLimitConvergence

------------------------------------------------------------------------
-- Exact residual frontier.
------------------------------------------------------------------------

record EisensteinBishopConvergenceFrontier : Set where
  constructor eisenstein-bishop-convergence-frontier
  field
    vendoredBishopBackendOwned : Bool
    finiteSumToBishopSeriesBridgeOwned : Bool
    absoluteConvergenceToLimitCompilerOwned : Bool
    bishopLimitUniquenessOwned : Bool
    bishopComplexComponentwiseConvergenceOwned : Bool
    concreteMurrayBishopSetoidBackendOwned : Bool
    bishopSetoidComplexAlgebraOwned : Bool
    bishopNatCoefficientEmbeddingBridgesOwned : Bool
    bishopSetoidEisensteinSeriesFromPowerEnvelopeOwned : Bool
    bishopComplexNormSquarePowerEnvelopeCompilerOwned : Bool
    bishopNonnegativeSquareReflectionInhabited : Bool
    bishopActualQNormSquareRadiusOwned : Bool
    bishopQPowerComponentEnvelopeInhabited : Bool
    bishopQFromUnitPhaseCompilerOwned : Bool
    bishopActualUnitPhaseOwned : Bool
    bishopUpperHalfPlaneEisensteinFromUnitPhaseOwned : Bool

    sameCarrierConcreteComplexLimitCompilerOwned : Bool
    eisensteinCoefficientPolynomialGrowthOwned : Bool
    literalTruncationIncrementIdentityOwned : Bool
    literalIncrementCoefficientEnvelopeOwned : Bool
    qPowerModulusPropagationCompilerOwned : Bool
    polynomialGeometricIncrementModulusCompilerOwned : Bool
    genericDominatedTailCompilerOwned : Bool
    bishopPolynomialGeometricComparisonCompilerOwned : Bool
    bishopStrictRatioInterpolationOwned : Bool
    bishopPolynomialSuccessorFactorLimitOwned : Bool
    bishopFixedDegreePolynomialGeometricConvergenceOwned : Bool
    bishopFixedDegreePolynomialGeometricAbsoluteConvergenceOwned : Bool
    bishopShiftedScaledPolynomialGeometricAbsoluteConvergenceOwned : Bool
    bishopEisensteinMajorantSpecializationOwned : Bool
    bishopLiteralRadiusMajorantCompilerOwned : Bool
    bishopLiteralRadiusWeldCompilerOwned : Bool
    bishopFiniteCauchyWingOwned : Bool
    bishopExponentialAdditivityOwned : Bool
    bishopGlobalNegativeExponentialUnitIntervalOwned : Bool
    bishopUpperHalfPlaneRadiusOwned : Bool
    bishopUpperHalfPlaneEisensteinMajorantsOwned : Bool
    bishopUpperHalfPlaneQuotientRadiusWeldCompilerOwned : Bool
    literalQToBishopRadiusReductionCompilerOwned : Bool
    qExponentMagnitudeToLiteralExponentCompilerOwned : Bool
    qMagnitudeCoordinateTransportCompilerOwned : Bool
    canonicalBishopQuotientRadiusRelationOwned : Bool
    literalQToBishopRadiusSameObjectOwned : Bool
    bishopDegreeFourPolynomialGeometricConvergenceOwned : Bool
    bishopDegreeSixPolynomialGeometricConvergenceOwned : Bool
    genericTailToCauchyBridgeOwned : Bool
    selectedTailToCauchyBridgeInhabited : Bool
    fastCauchyLegacyQuotientInterfaceWeldOwned : Bool
    genericSetoidComplexQuotientRingWeldOwned : Bool
    fastCauchySetQuotientComplexCompatibilityCompilerOwned : Bool
    concreteLegacyQuotientInhabited : Bool
    modulusMultiplicationFactorCompilerOwned : Bool
    complexNormSquareCompositionInhabited : Bool
    nonnegativeSquareRootMultiplicationInhabited : Bool
    sameCarrierModulusAlgebraInhabited : Bool
    principalStripQModulusCompilerOwned : Bool
    upperHalfPlaneQDecayCompilerOwned : Bool
    concreteQOrderAndStripInputsOwned : Bool

    -- This is specifically the Bishop-setoid -> legacy ConcreteComplex weld.
    -- The same-carrier route above avoids needing it.
    constructedComplexEvaluatorCarrierWeldOwned : Bool

    e4ConcreteAbsoluteConvergenceOwned : Bool
    e6ConcreteAbsoluteConvergenceOwned : Bool
    abstractEisensteinLatticeReindexingTransformationOwned : Bool
    concreteClassicalLatticeEisensteinModelOwned : Bool
    bishopLimitEqualsAnalyticLatticeEisenstein : Bool
    analyticKleinJPromotionOwned : Bool

    citationsCreateProofAuthority : Bool
    finitePythonParityCreatesConvergence : Bool
    reading : String

open EisensteinBishopConvergenceFrontier public

canonicalEisensteinBishopConvergenceFrontier :
  EisensteinBishopConvergenceFrontier
canonicalEisensteinBishopConvergenceFrontier = record
  { vendoredBishopBackendOwned = true
  ; finiteSumToBishopSeriesBridgeOwned = true
  ; absoluteConvergenceToLimitCompilerOwned = true
  ; bishopLimitUniquenessOwned = true
  ; bishopComplexComponentwiseConvergenceOwned = true
  ; concreteMurrayBishopSetoidBackendOwned = true
  ; bishopSetoidComplexAlgebraOwned = true
  ; bishopNatCoefficientEmbeddingBridgesOwned = true
  ; bishopSetoidEisensteinSeriesFromPowerEnvelopeOwned = true
  ; bishopComplexNormSquarePowerEnvelopeCompilerOwned = true
  ; bishopNonnegativeSquareReflectionInhabited = false
  ; bishopActualQNormSquareRadiusOwned = false
  ; bishopQPowerComponentEnvelopeInhabited = false
  ; bishopQFromUnitPhaseCompilerOwned = true
  ; bishopActualUnitPhaseOwned = false
  ; bishopUpperHalfPlaneEisensteinFromUnitPhaseOwned = true

  ; sameCarrierConcreteComplexLimitCompilerOwned = true
  ; eisensteinCoefficientPolynomialGrowthOwned = true
  ; literalTruncationIncrementIdentityOwned = true
  ; literalIncrementCoefficientEnvelopeOwned = true
  ; qPowerModulusPropagationCompilerOwned = true
  ; polynomialGeometricIncrementModulusCompilerOwned = true
  ; genericDominatedTailCompilerOwned = true
  ; bishopPolynomialGeometricComparisonCompilerOwned = true
  ; bishopStrictRatioInterpolationOwned = true
  ; bishopPolynomialSuccessorFactorLimitOwned = true
  ; bishopFixedDegreePolynomialGeometricConvergenceOwned = true
  ; bishopFixedDegreePolynomialGeometricAbsoluteConvergenceOwned = true
  ; bishopShiftedScaledPolynomialGeometricAbsoluteConvergenceOwned = true
  ; bishopEisensteinMajorantSpecializationOwned = true
  ; bishopLiteralRadiusMajorantCompilerOwned = true
  ; bishopLiteralRadiusWeldCompilerOwned = true
  ; bishopFiniteCauchyWingOwned = true
  ; bishopExponentialAdditivityOwned = true
  ; bishopGlobalNegativeExponentialUnitIntervalOwned = true
  ; bishopUpperHalfPlaneRadiusOwned = true
  ; bishopUpperHalfPlaneEisensteinMajorantsOwned = true
  ; bishopUpperHalfPlaneQuotientRadiusWeldCompilerOwned = true
  ; literalQToBishopRadiusReductionCompilerOwned = true
  ; qExponentMagnitudeToLiteralExponentCompilerOwned = true
  ; qMagnitudeCoordinateTransportCompilerOwned = true
  ; canonicalBishopQuotientRadiusRelationOwned = true
  ; literalQToBishopRadiusSameObjectOwned = false
  ; bishopDegreeFourPolynomialGeometricConvergenceOwned = true
  ; bishopDegreeSixPolynomialGeometricConvergenceOwned = true
  ; genericTailToCauchyBridgeOwned = true
  ; selectedTailToCauchyBridgeInhabited = false
  ; fastCauchyLegacyQuotientInterfaceWeldOwned = true
  ; genericSetoidComplexQuotientRingWeldOwned = true
  ; fastCauchySetQuotientComplexCompatibilityCompilerOwned = true
  ; concreteLegacyQuotientInhabited = false
  ; modulusMultiplicationFactorCompilerOwned = true
  ; complexNormSquareCompositionInhabited = false
  ; nonnegativeSquareRootMultiplicationInhabited = false
  ; sameCarrierModulusAlgebraInhabited = false
  ; principalStripQModulusCompilerOwned = true
  ; upperHalfPlaneQDecayCompilerOwned = true
  ; concreteQOrderAndStripInputsOwned = false
  ; constructedComplexEvaluatorCarrierWeldOwned = false
  ; e4ConcreteAbsoluteConvergenceOwned = false
  ; e6ConcreteAbsoluteConvergenceOwned = false
  ; abstractEisensteinLatticeReindexingTransformationOwned = true
  ; concreteClassicalLatticeEisensteinModelOwned = false
  ; bishopLimitEqualsAnalyticLatticeEisenstein = false
  ; analyticKleinJPromotionOwned = false
  ; citationsCreateProofAuthority = false
  ; finitePythonParityCreatesConvergence = false
  ; reading = "The nondegenerate Murray-Bishop setoid ordered-complete backend is concrete and its Cauchy completeness is already owned. The preferred analytic q-series route is now setoid-native: BishopComplex has the finite complex algebra needed by E4/E6, Nat coefficient inequalities transport canonically to Bishop reals, and the literal internal sigma3/sigma5 E4/E6 tails are componentwise absolutely convergent with canonical Bishop complex limits from any q object carrying a unit-radius component-power envelope. The all-n modular q(tau) power-component envelope is no longer primitive: normSq multiplicativity and power propagation are paid, and one normSq(q)=r^2 certificate plus nonnegative square-order reflection compile the entire envelope. The all-n q-power envelope is now further reduced: any unit Bishop complex phase, combined with the already-constructed upper-half-plane radius and square-order reflection, yields normSq(q)=r^2, the full power-component envelope, and canonical Bishop E4/E6 limits. The concrete square-reflection inhabitant and construction/identification of the actual unit phase of q(tau) remain unpaid. The older ConcreteComplex route is retained as a compatibility/runtime route: same-carrier Cauchy completion is paid, sigma3/sigma5 polynomial growth is paid, the exact E4/E6 successor increments and their 240/504 coefficient envelopes are paid; q-power modulus propagation and polynomial-times-geometric increment-modulus compilers are also paid. Generic dominated-tail vanishing is paid. More strongly, strict rational interpolation, the fixed-degree successor-factor limit, and the exact Bishop ratio-test weld now prove convergence of sum n^k r^n for every fixed natural degree k whenever 0<=r<1; nonnegativity upgrades that theorem to absolute convergence, and the literal Eisenstein-shaped scale*(n+1)^k*r^(n+1) family is also absolutely convergent for every nonnegative scale. The canonical Moonshine specializations 240(n+1)^4 r^(n+1) and 504(n+1)^6 r^(n+1) are now owned explicitly. The literal-radius -> Bishop-radius weld compiler is also paid: once a concrete quotient supplies the same-radius witness and Bishop unit-interval certificate, both majorant absolute-convergence receipts follow immediately. The finite Bishop Cauchy-wing estimate, concrete all-real exponential additivity, global negative-exponential unit-interval law, and positive-upper-half-plane Bishop q-radius construction are now also source-owned; from positive Bishop pi and positive Bishop imaginary coordinate, the canonical E4/E6 majorant families are absolutely convergent. A proof-relevant literal-radius -> Bishop-majorant compiler is owned, and any concrete Murray/Bishop propositional quotient induces the same-radius relation canonically by quotient equality with reflexive witness. The positive-upper-half-plane Bishop radius also composes canonically through any concrete Bishop propositional quotient into the radius-weld/majorant receipt. More strongly, the literal legacy |q(tau)| same-object problem is now reduced proof-relevantly to two real transports only: agreement of the single negative real exponent with Re((2*pi*i)tau), and agreement of the real exponential at that exponent. The principal-strip modulus theorem then compiles the literal complex modulus to the Bishop radius automatically. The exponent transport is itself now compiled from positive-magnitude same-object agreement plus negation preservation and the already-owned Cartesian normalization. The positive-magnitude agreement is further compiled from Bishop-to-legacy agreement of 2, pi, and Im(tau) plus multiplication preservation, using only the legacy distributive/unit laws. The positive-magnitude agreement and the real exponential agreement are not manufactured here, so the actual same-object theorem remains false. Degrees 4 and 6 are direct specializations rather than remaining analytic assumptions. The Step-V polynomial/geometric domination surface is also independently welded to the Bishop comparison theorem. The generic tail-to-IsCauchy bridge remains available for the legacy same-carrier route. The old Fast-Cauchy quotient realization is also welded definition-for-definition into the newer backend quotient seam. Generic componentwise setoid-complex -> propositional-quotient ConcreteComplex ring transport is now paid for zero/one/add/sub/mul/conjugation/norm-square once explicit quotient-operation compatibility is supplied, and for quotients built through the existing FastCauchy SetQuotient eliminators that compatibility is now compiled directly from lift₁/lift₂ beta laws, while an actual concrete legacy quotient / selected tail-to-Cauchy inhabitant remains unpaid. Ordinary modulus multiplication is now factored by a paid compiler into quadratic norm composition plus nonnegative-square-root multiplication/proof-independence; both concrete input families remain unpaid, and triangle/order remains an independent same-carrier inhabitant, and principal-strip/upper-half-plane q-decay compilers remain paid conditionally. The preferred-route q-specific input is now a concrete Bishop q(tau) together with its component-power envelope against the already-constructed Bishop radius; this can be paid by a setoid-native phase/modulus theorem without any propositional quotient. Legacy order/polar/quotient machinery remains relevant only for compatibility with the old ConcreteComplex evaluator. After constructing the actual Bishop q object/envelope, the next stage has two distinct payments: instantiate the repository's abstract EisensteinAnalyticModel with the actual classical Bishop-complex lattice sum/summand semantics, then identify the Bishop q-series E4/E6 limits with that concrete lattice model. The SL2(Z) lattice-bijection/reindexing transformation theorem itself is already owned abstractly, but no independent concrete classical EisensteinAnalyticModel inhabitant was found. Generic polynomial-geometric summability is no longer part of the analytic min-cut."
  }
