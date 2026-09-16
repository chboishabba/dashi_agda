{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116CanonicalSubstitutionContractionRateRound367Exact where

------------------------------------------------------------------------
-- ROUND367 / CANONICAL SUBSTITUTED-BACKGROUND CONTRACTION-RATE CANDIDATE
--
-- Round104 already extracts four normalized CMP116 analytic demands and picks
-- one common radius epsilon_* paying all four.  In particular it proves
--
--   substitutedBackgroundDemand * epsilon_* < 1.
--
-- Therefore strict scalar smallness for the substituted-background fixed-point
-- construction is compiler-owned once the finite source demand is supplied.
-- What remains source/same-object specific is the theorem that THIS normalized
-- demand actually majorizes the Lipschitz constant of the literal CMP116 map.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; 1ℚ; _*_; _<_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP116CanonicalCommonRadiusRound104Exact as R104

canonicalSubstitutionContractionRate :
  R104.CMP116FiniteNormalizedAnalyticDemands → ℚ
canonicalSubstitutionContractionRate dataSet =
  R104.substitutedBackgroundDemand dataSet
    * R104.canonicalCommonRadius dataSet

canonicalSubstitutionContractionRateStrict :
  (dataSet : R104.CMP116FiniteNormalizedAnalyticDemands) →
  canonicalSubstitutionContractionRate dataSet < 1ℚ
canonicalSubstitutionContractionRateStrict dataSet =
  R104.substitutedBackgroundDemandPaid dataSet

------------------------------------------------------------------------
-- Same-object source attachment.
------------------------------------------------------------------------

record LiteralCMP116SubstitutionContractionAttachment
    (dataSet : R104.CMP116FiniteNormalizedAnalyticDemands) : Set₁ where
  field
    State : Set
    literalSubstitutionMap : State → State

    -- Consumer-owned meaning of a quantitative contraction statement on the
    -- literal map.  Keeping the map and rate as indices prevents the source
    -- theorem from being detached from the object/rate it is supposed to pay.
    ContractionAtRate : (State → State) → ℚ → Set

    literalMapContractsAtCanonicalRate :
      ContractionAtRate
        literalSubstitutionMap
        (canonicalSubstitutionContractionRate dataSet)

open LiteralCMP116SubstitutionContractionAttachment public

canonicalRateStrictnessCompilerLevel : ProofLevel
canonicalRateStrictnessCompilerLevel = machineChecked

literalCMP116NormalizedDemandExtractionLevel : ProofLevel
literalCMP116NormalizedDemandExtractionLevel = conditional

literalCMP116MapLipschitzAttachmentLevel : ProofLevel
literalCMP116MapLipschitzAttachmentLevel = conditional

newIndependentStrictContractionConstantRequired : Bool
newIndependentStrictContractionConstantRequired = false

newIndependentStrictContractionConstantRequiredIsFalse :
  newIndependentStrictContractionConstantRequired ≡ false
newIndependentStrictContractionConstantRequiredIsFalse = refl

canonicalDemandAloneProvesLiteralMapContraction : Bool
canonicalDemandAloneProvesLiteralMapContraction = false

canonicalDemandAloneProvesLiteralMapContractionIsFalse :
  canonicalDemandAloneProvesLiteralMapContraction ≡ false
canonicalDemandAloneProvesLiteralMapContractionIsFalse = refl

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
