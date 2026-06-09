module DASHI.Physics.Closure.NSLargeDataGapCorrectionReceipt where

open import Agda.Primitive using (Set; Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.NSLargeDataContractionInputRequest as Input

------------------------------------------------------------------------
-- Correction receipt for the prior NS large-data contraction framing.
--
-- The previous request framed the remaining large-data Navier-Stokes gap as
-- a contraction target.  This receipt retires that framing: contraction is
-- only a small-data method.  The corrected large-data gap is a global energy
-- bound / small-viscosity cross-lane case.  For nu > C_cross this records a
-- large-data regularity candidate; for nu <= C_cross the case remains open.
-- No smooth global regularity theorem, Clay Navier-Stokes promotion, or
-- terminal Clay promotion is made here.

data NSLargeDataGapCorrectionStatus : Set where
  contractionFramingRetiredGapCorrectedNoClayPromotion :
    NSLargeDataGapCorrectionStatus

data NSLargeDataCorrectGapStatement : Set where
  smallViscosityCrossLaneCase :
    NSLargeDataCorrectGapStatement

data NSLargeDataGapCorrectionItem : Set where
  priorContractionRequestCorrected :
    NSLargeDataGapCorrectionItem

  contractionSmallDataOnly :
    NSLargeDataGapCorrectionItem

  globalEnergyBoundCrossLaneGap :
    NSLargeDataGapCorrectionItem

  nuAboveCrossThresholdCandidate :
    NSLargeDataGapCorrectionItem

  nuAtOrBelowCrossThresholdOpen :
    NSLargeDataGapCorrectionItem

canonicalNSLargeDataGapCorrectionItems :
  List NSLargeDataGapCorrectionItem
canonicalNSLargeDataGapCorrectionItems =
  priorContractionRequestCorrected
  ∷ contractionSmallDataOnly
  ∷ globalEnergyBoundCrossLaneGap
  ∷ nuAboveCrossThresholdCandidate
  ∷ nuAtOrBelowCrossThresholdOpen
  ∷ []

data NSLargeDataGapCorrectionPromotion : Set where

nsLargeDataGapCorrectionPromotionImpossibleHere :
  NSLargeDataGapCorrectionPromotion →
  ⊥
nsLargeDataGapCorrectionPromotionImpossibleHere ()

nsLargeDataGapCorrectionStatement : String
nsLargeDataGapCorrectionStatement =
  "Correction of NSLargeDataContractionInputRequest: large-data contraction framing is retired because contraction is small-data only.  The corrected large-data gap is the global energy bound / small-viscosity cross-lane case: nu > C_cross is recorded as a large-data regularity candidate, while nu <= C_cross remains open.  All Clay promotion flags remain false."

record NSLargeDataGapCorrectionReceipt : Setω where
  field
    status :
      NSLargeDataGapCorrectionStatus

    correctionOf :
      Input.NSLargeDataContractionInputRequest

    correctionOfIsNSLargeDataContractionInputRequest :
      Bool

    correctionOfIsNSLargeDataContractionInputRequestIsTrue :
      correctionOfIsNSLargeDataContractionInputRequest ≡ true

    correctGapStatement :
      NSLargeDataCorrectGapStatement

    correctGapStatementIsSmallViscosityCrossLaneCase :
      correctGapStatement ≡ smallViscosityCrossLaneCase

    correctionItems :
      List NSLargeDataGapCorrectionItem

    correctionItemsAreCanonical :
      correctionItems ≡ canonicalNSLargeDataGapCorrectionItems

    contractionFramingRetired :
      Bool

    contractionFramingRetiredIsTrue :
      contractionFramingRetired ≡ true

    contractionIsSmallDataOnly :
      Bool

    contractionIsSmallDataOnlyIsTrue :
      contractionIsSmallDataOnly ≡ true

    largeDataContractionTargetRetired :
      Bool

    largeDataContractionTargetRetiredIsTrue :
      largeDataContractionTargetRetired ≡ true

    correctedGapIsGlobalEnergyBound :
      Bool

    correctedGapIsGlobalEnergyBoundIsTrue :
      correctedGapIsGlobalEnergyBound ≡ true

    correctedGapIsSmallViscosityCrossLaneCase :
      Bool

    correctedGapIsSmallViscosityCrossLaneCaseIsTrue :
      correctedGapIsSmallViscosityCrossLaneCase ≡ true

    nuGreaterThanCCrossLargeDataRegularityCandidate :
      Bool

    nuGreaterThanCCrossLargeDataRegularityCandidateIsTrue :
      nuGreaterThanCCrossLargeDataRegularityCandidate ≡ true

    nuLessOrEqualCCrossRemainsOpen :
      Bool

    nuLessOrEqualCCrossRemainsOpenIsTrue :
      nuLessOrEqualCCrossRemainsOpen ≡ true

    largeDataRegularityTheoremConstructed :
      Bool

    largeDataRegularityTheoremConstructedIsFalse :
      largeDataRegularityTheoremConstructed ≡ false

    globalEnergyBoundConstructed :
      Bool

    globalEnergyBoundConstructedIsFalse :
      globalEnergyBoundConstructed ≡ false

    smoothGlobalRegularityPromoted :
      Bool

    smoothGlobalRegularityPromotedIsFalse :
      smoothGlobalRegularityPromoted ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    allClayPromotionFlagsFalse :
      Bool

    allClayPromotionFlagsFalseIsTrue :
      allClayPromotionFlagsFalse ≡ true

    statement :
      String

    statementIsCanonical :
      statement ≡ nsLargeDataGapCorrectionStatement

    promotionFlags :
      List NSLargeDataGapCorrectionPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open NSLargeDataGapCorrectionReceipt public

canonicalNSLargeDataGapCorrectionReceipt :
  NSLargeDataGapCorrectionReceipt
canonicalNSLargeDataGapCorrectionReceipt =
  record
    { status =
        contractionFramingRetiredGapCorrectedNoClayPromotion
    ; correctionOf =
        Input.canonicalNSLargeDataContractionInputRequest
    ; correctionOfIsNSLargeDataContractionInputRequest =
        true
    ; correctionOfIsNSLargeDataContractionInputRequestIsTrue =
        refl
    ; correctGapStatement =
        smallViscosityCrossLaneCase
    ; correctGapStatementIsSmallViscosityCrossLaneCase =
        refl
    ; correctionItems =
        canonicalNSLargeDataGapCorrectionItems
    ; correctionItemsAreCanonical =
        refl
    ; contractionFramingRetired =
        true
    ; contractionFramingRetiredIsTrue =
        refl
    ; contractionIsSmallDataOnly =
        true
    ; contractionIsSmallDataOnlyIsTrue =
        refl
    ; largeDataContractionTargetRetired =
        true
    ; largeDataContractionTargetRetiredIsTrue =
        refl
    ; correctedGapIsGlobalEnergyBound =
        true
    ; correctedGapIsGlobalEnergyBoundIsTrue =
        refl
    ; correctedGapIsSmallViscosityCrossLaneCase =
        true
    ; correctedGapIsSmallViscosityCrossLaneCaseIsTrue =
        refl
    ; nuGreaterThanCCrossLargeDataRegularityCandidate =
        true
    ; nuGreaterThanCCrossLargeDataRegularityCandidateIsTrue =
        refl
    ; nuLessOrEqualCCrossRemainsOpen =
        true
    ; nuLessOrEqualCCrossRemainsOpenIsTrue =
        refl
    ; largeDataRegularityTheoremConstructed =
        false
    ; largeDataRegularityTheoremConstructedIsFalse =
        refl
    ; globalEnergyBoundConstructed =
        false
    ; globalEnergyBoundConstructedIsFalse =
        refl
    ; smoothGlobalRegularityPromoted =
        false
    ; smoothGlobalRegularityPromotedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; allClayPromotionFlagsFalse =
        true
    ; allClayPromotionFlagsFalseIsTrue =
        refl
    ; statement =
        nsLargeDataGapCorrectionStatement
    ; statementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "correctionOf = NSLargeDataContractionInputRequest"
        ∷ "correctGapStatement = smallViscosityCrossLaneCase"
        ∷ "contractionFramingRetired = true"
        ∷ "Contraction is retained only as a small-data method"
        ∷ "The corrected large-data gap is global energy bound / small-viscosity cross-lane control"
        ∷ "nu > C_cross records a large-data regularity candidate"
        ∷ "nu <= C_cross remains open"
        ∷ "All Clay promotion flags are false"
        ∷ []
    }

nsLargeDataGapCorrectionRetiresContractionFraming :
  contractionFramingRetired canonicalNSLargeDataGapCorrectionReceipt
  ≡
  true
nsLargeDataGapCorrectionRetiresContractionFraming =
  refl

nsLargeDataGapCorrectionCorrectGap :
  correctGapStatement canonicalNSLargeDataGapCorrectionReceipt
  ≡
  smallViscosityCrossLaneCase
nsLargeDataGapCorrectionCorrectGap =
  refl

nsLargeDataGapCorrectionKeepsClayFalse :
  clayNavierStokesPromoted canonicalNSLargeDataGapCorrectionReceipt
  ≡
  false
nsLargeDataGapCorrectionKeepsClayFalse =
  refl

nsLargeDataGapCorrectionNoPromotion :
  NSLargeDataGapCorrectionPromotion →
  ⊥
nsLargeDataGapCorrectionNoPromotion =
  nsLargeDataGapCorrectionPromotionImpossibleHere
