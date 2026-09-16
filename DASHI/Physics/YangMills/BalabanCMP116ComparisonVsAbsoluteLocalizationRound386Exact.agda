{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116ComparisonVsAbsoluteLocalizationRound386Exact where

------------------------------------------------------------------------
-- ROUND386 / COMPARISON IS NOT AN ABSOLUTE LOCALIZATION ANCHOR
--
-- R385 is now a very small and useful producer:
--
--   ||H_left - H_right|| <= L_Hessian * U_par.
--
-- The canonical B consumer, however, is R346/R338/R341's absolute selected
-- response localization:
--
--   |D^2_{J_L,J_R} log Z| <= selected rooted/source envelope.
--
-- These are not the same theorem.  A difference estimate alone cannot bound the
-- absolute level of either endpoint: equal nonzero endpoints have zero
-- difference.  Therefore R385 may feed the terminal localization only together
-- with an actual same-object coefficient attachment AND either an absolute
-- reference/anchor payment or the already-source-owned absolute differentiated
-- localization theorem.
--
-- This is a WrongType/FactorsThrough firewall, not a new analytic estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Data.Nat using (_≤_; _∸_; z≤n)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanCMP116MinimalDistanceLiteralHessianRound385Exact as R385
import DASHI.Physics.YangMills.BalabanCMP116SharedMarkedAmplitudeDirectRound346Exact as R346
import DASHI.Physics.YangMills.BalabanCMP116SelectedCoefficientAttachmentRound348Exact as R348
import DASHI.Physics.YangMills.BalabanCMP116CanonicalCommonDomainSourceRound338Exact as R338
import DASHI.Physics.YangMills.BalabanCMP116R281ModeSelectedDirectRound341Exact as R341

------------------------------------------------------------------------
-- Tiny exact counterexample: no generic rule can promote endpoint difference
-- control to absolute endpoint control without another coordinate.
------------------------------------------------------------------------

record DifferenceOnlyPromotesAbsolute : Set where
  constructor difference-only-promotes-absolute
  field
    promote :
      ∀ selected reference upper : Nat →
      selected ∸ reference ≤ upper →
      selected ≤ upper

open DifferenceOnlyPromotesAbsolute public

differenceOnlyPromotionImpossible : DifferenceOnlyPromotesAbsolute → ⊥
differenceOnlyPromotionImpossible promotion with
  promote promotion (suc zero) (suc zero) zero z≤n
... | ()

------------------------------------------------------------------------
-- Current physical/YM interpretation.
------------------------------------------------------------------------

coefficientComparisonProducerLevel : ProofLevel
coefficientComparisonProducerLevel = R385.round385DirectMinimalCompositionLevel

selectedCoefficientSameObjectLevel : ProofLevel
selectedCoefficientSameObjectLevel = R348.selectedCoefficientSameObjectLevel

literalAbsoluteSelectedLocalizationLevel : ProofLevel
literalAbsoluteSelectedLocalizationLevel = R346.round346LiteralSelectedLocalizationLevel

canonicalCMP116SourceAlignmentLevel : ProofLevel
canonicalCMP116SourceAlignmentLevel = R338.round338LocalCanonicalSourceAlignmentLevel

modeSelectedSourceResponseSameObjectLevel : ProofLevel
modeSelectedSourceResponseSameObjectLevel = R341.round341SourceResponseSameObjectLevel

modeSelectedEnvelopeCalibrationLevel : ProofLevel
modeSelectedEnvelopeCalibrationLevel = R341.round341EnvelopeCalibrationLevel

comparisonAlonePaysAbsoluteLocalization : Bool
comparisonAlonePaysAbsoluteLocalization = false

comparisonAlonePaysAbsoluteLocalizationIsFalse :
  comparisonAlonePaysAbsoluteLocalization ≡ false
comparisonAlonePaysAbsoluteLocalizationIsFalse = refl

coefficientSameObjectAlonePaysAbsoluteLocalization : Bool
coefficientSameObjectAlonePaysAbsoluteLocalization = false

coefficientSameObjectAlonePaysAbsoluteLocalizationIsFalse :
  coefficientSameObjectAlonePaysAbsoluteLocalization ≡ false
coefficientSameObjectAlonePaysAbsoluteLocalizationIsFalse = refl

absoluteReferenceOrSourceLocalizationStillNeeded : Bool
absoluteReferenceOrSourceLocalizationStillNeeded = true

absoluteReferenceOrSourceLocalizationStillNeededIsTrue :
  absoluteReferenceOrSourceLocalizationStillNeeded ≡ true
absoluteReferenceOrSourceLocalizationStillNeededIsTrue = refl

r385MandatoryForCanonicalB : Bool
r385MandatoryForCanonicalB = false

r385MandatoryForCanonicalBIsFalse : r385MandatoryForCanonicalB ≡ false
r385MandatoryForCanonicalBIsFalse = refl

record Round386Boundary : Set where
  constructor round386-boundary
  field
    differenceToAbsolutePromotionRefutedGenerically : Bool
    differenceToAbsolutePromotionRefutedGenericallyIsTrue :
      differenceToAbsolutePromotionRefutedGenerically ≡ true

    directSourceAbsoluteLocalizationRemainsValidProducer : Bool
    directSourceAbsoluteLocalizationRemainsValidProducerIsTrue :
      directSourceAbsoluteLocalizationRemainsValidProducer ≡ true

    coefficientSensitivityRemainsOptionalSubproducer : Bool
    coefficientSensitivityRemainsOptionalSubproducerIsTrue :
      coefficientSensitivityRemainsOptionalSubproducer ≡ true

canonicalRound386Boundary : Round386Boundary
canonicalRound386Boundary =
  round386-boundary true refl true refl true refl

round386FrontierRefinementLevel : ProofLevel
round386FrontierRefinementLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
