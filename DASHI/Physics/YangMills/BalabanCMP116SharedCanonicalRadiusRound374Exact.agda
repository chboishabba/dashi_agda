module DASHI.Physics.YangMills.BalabanCMP116SharedCanonicalRadiusRound374Exact where

------------------------------------------------------------------------
-- ROUND374 / ONE CMP116 CANONICAL RADIUS, TWO CONSUMER INTERPRETATIONS
--
-- Round114 already constructs ONE positive rational analytic radius from the
-- finite normalized CMP116 Sect.1 demands and proves that the same radius
-- supports first- and second-derivative Cauchy use.  R371 and R372, however,
-- expose real-valued `PositiveRadiusMargin` predicates through the generic R370
-- sensitivity authority.
--
-- This owner removes the accidental duplication of the radius SCALAR.  It uses
-- the existing strict-order-preserving Q -> R embedding to produce one positive
-- real radius, then asks only for application-specific interpretations of that
-- SAME value in the fixed-point and Hessian Cauchy consumers.
--
-- Important firewall: `PositiveRadiusMargin` is abstract in R370.  Therefore
-- real positivity cannot definitionally create either margin predicate.  The
-- two interpretation maps below are representation/application welds; they are
-- not two independent radius-existence or positivity theorems.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 0ℝ; _<ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanCMP116CanonicalCommonRadiusRound104Exact as Canon
import DASHI.Physics.YangMills.BalabanCMP116CanonicalRadiusToCommonDomainRound114Exact as R114
import DASHI.Physics.YangMills.BalabanCMP116CommonAnalyticRadiusRound103Exact as Common
import DASHI.Physics.YangMills.BalabanCMP116DirectParametricSensitivityRound370Exact as R370
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Embed

------------------------------------------------------------------------
-- One physical/source radius coordinate shared by both derivative consumers.
------------------------------------------------------------------------

record SharedCanonicalRadiusData : Set₁ where
  field
    Scale Volume : Set
    analyticDemands : Canon.CMP116FiniteNormalizedAnalyticDemands
    embedding : Embed.OrderedRationalRealEmbedding

    FixedParameter FixedBackground : Set
    fixedSensitivity :
      R370.CauchyParametricSensitivityAuthority
        FixedParameter FixedBackground

    HessianParameter HessianValue : Set
    hessianSensitivity :
      R370.CauchyParametricSensitivityAuthority
        HessianParameter HessianValue

    -- R370 deliberately leaves PositiveRadiusMargin abstract.  These two maps
    -- only explain how ordinary strict positivity of the SAME source radius is
    -- interpreted by each selected Cauchy consumer.
    fixedMarginFromPositive :
      ∀ radius → 0ℝ <ℝ radius →
      R370.PositiveRadiusMargin fixedSensitivity radius

    hessianMarginFromPositive :
      ∀ radius → 0ℝ <ℝ radius →
      R370.PositiveRadiusMargin hessianSensitivity radius

open SharedCanonicalRadiusData public

canonicalSourceRadius :
  (dataSet : SharedCanonicalRadiusData) →
  Common.CMP116CommonAnalyticRadius
    (Scale dataSet) (Volume dataSet)
canonicalSourceRadius dataSet =
  R114.canonicalCMP116CommonDomain (analyticDemands dataSet)

canonicalDerivativeRadiusUse :
  (dataSet : SharedCanonicalRadiusData) →
  Common.FirstSecondDerivativeUseSameRadius (canonicalSourceRadius dataSet)
canonicalDerivativeRadiusUse dataSet =
  R114.canonicalFirstSecondDerivativeSameRadius (analyticDemands dataSet)

canonicalRealRadius : SharedCanonicalRadiusData → ℝ
canonicalRealRadius dataSet =
  Embed.embed (embedding dataSet)
    (Common.radius (canonicalSourceRadius dataSet))

canonicalRealRadiusPositive :
  (dataSet : SharedCanonicalRadiusData) →
  0ℝ <ℝ canonicalRealRadius dataSet
canonicalRealRadiusPositive dataSet =
  subst
    (λ left → left <ℝ canonicalRealRadius dataSet)
    (Embed.zeroExact (embedding dataSet))
    (Embed.strictOrderPreserving (embedding dataSet)
      (Common.radiusPositive (canonicalSourceRadius dataSet)))

fixedPointRadiusMargin :
  (dataSet : SharedCanonicalRadiusData) →
  R370.PositiveRadiusMargin
    (fixedSensitivity dataSet) (canonicalRealRadius dataSet)
fixedPointRadiusMargin dataSet =
  fixedMarginFromPositive dataSet
    (canonicalRealRadius dataSet)
    (canonicalRealRadiusPositive dataSet)

hessianRadiusMargin :
  (dataSet : SharedCanonicalRadiusData) →
  R370.PositiveRadiusMargin
    (hessianSensitivity dataSet) (canonicalRealRadius dataSet)
hessianRadiusMargin dataSet =
  hessianMarginFromPositive dataSet
    (canonicalRealRadius dataSet)
    (canonicalRealRadiusPositive dataSet)

------------------------------------------------------------------------
-- Pareto / authority boundary.
------------------------------------------------------------------------

canonicalFiniteDemandRadiusConstructionLevel : ProofLevel
canonicalFiniteDemandRadiusConstructionLevel =
  R114.cmp116FiniteDemandsToCommonRadiusObjectLevel

canonicalFirstSecondDerivativeSharedRadiusLevel : ProofLevel
canonicalFirstSecondDerivativeSharedRadiusLevel =
  R114.cmp116FirstSecondDerivativeShareCanonicalRadiusLevel

orderedRationalRealRadiusEmbeddingLevel : ProofLevel
orderedRationalRealRadiusEmbeddingLevel = Embed.orderedRationalRealEmbeddingLevel

sharedRealRadiusPositivityCompilerLevel : ProofLevel
sharedRealRadiusPositivityCompilerLevel = machineChecked

fixedPointRadiusInterpretationLevel : ProofLevel
fixedPointRadiusInterpretationLevel = conditional

hessianRadiusInterpretationLevel : ProofLevel
hessianRadiusInterpretationLevel = conditional

twoIndependentRadiusScalarsRequiredAfterRound374 : Bool
twoIndependentRadiusScalarsRequiredAfterRound374 = false

twoIndependentRadiusScalarsRequiredAfterRound374IsFalse :
  twoIndependentRadiusScalarsRequiredAfterRound374 ≡ false
twoIndependentRadiusScalarsRequiredAfterRound374IsFalse = refl

radiusInterpretationStillApplicationSpecific : Bool
radiusInterpretationStillApplicationSpecific = true

radiusInterpretationStillApplicationSpecificIsTrue :
  radiusInterpretationStillApplicationSpecific ≡ true
radiusInterpretationStillApplicationSpecificIsTrue = refl

record Round374Boundary : Set where
  constructor round374-boundary
  field
    oneFiniteDemandPackageBuildsSharedSourceRadius : Bool
    oneFiniteDemandPackageBuildsSharedSourceRadiusIsTrue :
      oneFiniteDemandPackageBuildsSharedSourceRadius ≡ true

    oneEmbeddedRealRadiusFeedsFirstAndSecondDerivativeConsumers : Bool
    oneEmbeddedRealRadiusFeedsFirstAndSecondDerivativeConsumersIsTrue :
      oneEmbeddedRealRadiusFeedsFirstAndSecondDerivativeConsumers ≡ true

    genericR370MarginPredicateMayBeCollapsedToPositivity : Bool
    genericR370MarginPredicateMayBeCollapsedToPositivityIsFalse :
      genericR370MarginPredicateMayBeCollapsedToPositivity ≡ false

canonicalRound374Boundary : Round374Boundary
canonicalRound374Boundary =
  round374-boundary true refl true refl false refl

round374FrontierRefinementLevel : ProofLevel
round374FrontierRefinementLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
