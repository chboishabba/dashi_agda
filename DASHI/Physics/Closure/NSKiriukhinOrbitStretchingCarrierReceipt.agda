module DASHI.Physics.Closure.NSKiriukhinOrbitStretchingCarrierReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Fail-closed receipt for the Kiriukhin orbit-level stretching matrix route.
--
-- This module records the orbit-level symmetric stretching matrix V_N as a
-- candidate carrier, but only at model level.  The ensemble spectral decay
-- input is explicitly treated as model-only bookkeeping, and the orbit
-- continuation criterion is recorded as an external/model-level input rather
-- than a proved bridge.  No full NS or Clay promotion is made here.

data NSKiriukhinOrbitStretchingCarrierStatus : Set where
  orbitLevelCarrierRouteRecorded_modelOnly_noPromotion :
    NSKiriukhinOrbitStretchingCarrierStatus

data NSKiriukhinOrbitStretchingCarrierItem : Set where
  orbitLevelSymmetricStretchingMatrixRecorded :
    NSKiriukhinOrbitStretchingCarrierItem

  candidateCarrierNotationVnRecorded :
    NSKiriukhinOrbitStretchingCarrierItem

  symmetricStretchingRecorded :
    NSKiriukhinOrbitStretchingCarrierItem

  ensembleSpectralDecayModelOnlyRecorded :
    NSKiriukhinOrbitStretchingCarrierItem

  orbitContinuationCriterionExternalInputRecorded :
    NSKiriukhinOrbitStretchingCarrierItem

  orbitContinuationCriterionModelLevelRecorded :
    NSKiriukhinOrbitStretchingCarrierItem

  fullNSPromotionGateClosedRecorded :
    NSKiriukhinOrbitStretchingCarrierItem

  clayPromotionGateClosedRecorded :
    NSKiriukhinOrbitStretchingCarrierItem

  modelBoundaryRecorded :
    NSKiriukhinOrbitStretchingCarrierItem

canonicalNSKiriukhinOrbitStretchingCarrierItems :
  List NSKiriukhinOrbitStretchingCarrierItem
canonicalNSKiriukhinOrbitStretchingCarrierItems =
  orbitLevelSymmetricStretchingMatrixRecorded
  ∷ candidateCarrierNotationVnRecorded
  ∷ symmetricStretchingRecorded
  ∷ ensembleSpectralDecayModelOnlyRecorded
  ∷ orbitContinuationCriterionExternalInputRecorded
  ∷ orbitContinuationCriterionModelLevelRecorded
  ∷ fullNSPromotionGateClosedRecorded
  ∷ clayPromotionGateClosedRecorded
  ∷ modelBoundaryRecorded
  ∷ []

data NSKiriukhinOrbitStretchingScope : Set where
  orbitLevelCarrierMatrixVn :
    NSKiriukhinOrbitStretchingScope

  symmetricOrbitLevelCarrierMatrix :
    NSKiriukhinOrbitStretchingScope

  ensembleSpectralDecayModelOnly :
    NSKiriukhinOrbitStretchingScope

  orbitContinuationCriterionExternalModelInput :
    NSKiriukhinOrbitStretchingScope

  failClosedNoFullNsPromotion :
    NSKiriukhinOrbitStretchingScope

  failClosedNoClayPromotion :
    NSKiriukhinOrbitStretchingScope

canonicalNSKiriukhinOrbitStretchingScope :
  List NSKiriukhinOrbitStretchingScope
canonicalNSKiriukhinOrbitStretchingScope =
  orbitLevelCarrierMatrixVn
  ∷ symmetricOrbitLevelCarrierMatrix
  ∷ ensembleSpectralDecayModelOnly
  ∷ orbitContinuationCriterionExternalModelInput
  ∷ failClosedNoFullNsPromotion
  ∷ failClosedNoClayPromotion
  ∷ []

data NSKiriukhinOrbitStretchingGap : Set where
  modelToFullNSContinuationGap :
    NSKiriukhinOrbitStretchingGap

  modelToClayPromotionGap :
    NSKiriukhinOrbitStretchingGap

  externalContinuationCriterionGap :
    NSKiriukhinOrbitStretchingGap

canonicalNSKiriukhinOrbitStretchingGaps :
  List NSKiriukhinOrbitStretchingGap
canonicalNSKiriukhinOrbitStretchingGaps =
  modelToFullNSContinuationGap
  ∷ modelToClayPromotionGap
  ∷ externalContinuationCriterionGap
  ∷ []

data NSKiriukhinOrbitStretchingPromotion : Set where

nsKiriukhinOrbitStretchingPromotionImpossibleHere :
  NSKiriukhinOrbitStretchingPromotion →
  ⊥
nsKiriukhinOrbitStretchingPromotionImpossibleHere ()

nsKiriukhinOrbitStretchingCarrierStatement : String
nsKiriukhinOrbitStretchingCarrierStatement =
  "Kiriukhin orbit-level route: the symmetric stretching matrix V_N is recorded as a candidate carrier in model-only form. Ensemble spectral decay is bookkeeping only, and the orbit continuation criterion is external/model-level input. The bridge to full NS and Clay remains closed."

record NSKiriukhinOrbitStretchingCarrierReceipt : Setω where
  field
    status :
      NSKiriukhinOrbitStretchingCarrierStatus

    statusIsCanonical :
      status ≡ orbitLevelCarrierRouteRecorded_modelOnly_noPromotion

    carrierItems :
      List NSKiriukhinOrbitStretchingCarrierItem

    carrierItemsAreCanonical :
      carrierItems ≡ canonicalNSKiriukhinOrbitStretchingCarrierItems

    carrierScope :
      List NSKiriukhinOrbitStretchingScope

    carrierScopeIsCanonical :
      carrierScope ≡ canonicalNSKiriukhinOrbitStretchingScope

    openGaps :
      List NSKiriukhinOrbitStretchingGap

    openGapsAreCanonical :
      openGaps ≡ canonicalNSKiriukhinOrbitStretchingGaps

    carrierMatrixNotation :
      String

    carrierMatrixNotationIsCanonical :
      carrierMatrixNotation ≡ "V_N"

    orbitLevelSymmetricStretchingMatrix :
      Bool

    orbitLevelSymmetricStretchingMatrixIsTrue :
      orbitLevelSymmetricStretchingMatrix ≡ true

    candidateCarrierRecorded :
      Bool

    candidateCarrierRecordedIsTrue :
      candidateCarrierRecorded ≡ true

    symmetricStretchingMarked :
      Bool

    symmetricStretchingMarkedIsTrue :
      symmetricStretchingMarked ≡ true

    ensembleSpectralDecayModelOnlyFlag :
      Bool

    ensembleSpectralDecayModelOnlyFlagIsTrue :
      ensembleSpectralDecayModelOnlyFlag ≡ true

    orbitContinuationCriterionExternalInput :
      Bool

    orbitContinuationCriterionExternalInputIsTrue :
      orbitContinuationCriterionExternalInput ≡ true

    orbitContinuationCriterionModelLevel :
      Bool

    orbitContinuationCriterionModelLevelIsTrue :
      orbitContinuationCriterionModelLevel ≡ true

    fullNSPromotionGateClosed :
      Bool

    fullNSPromotionGateClosedIsTrue :
      fullNSPromotionGateClosed ≡ true

    clayPromotionGateClosed :
      Bool

    clayPromotionGateClosedIsTrue :
      clayPromotionGateClosed ≡ true

    fullNSPromoted :
      Bool

    fullNSPromotedIsFalse :
      fullNSPromoted ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    modelToFullNSContinuationGapOpen :
      Bool

    modelToFullNSContinuationGapOpenIsTrue :
      modelToFullNSContinuationGapOpen ≡ true

    modelToClayPromotionGapOpen :
      Bool

    modelToClayPromotionGapOpenIsTrue :
      modelToClayPromotionGapOpen ≡ true

    externalContinuationCriterionGapOpen :
      Bool

    externalContinuationCriterionGapOpenIsTrue :
      externalContinuationCriterionGapOpen ≡ true

    statement :
      String

    statementIsCanonical :
      statement ≡ nsKiriukhinOrbitStretchingCarrierStatement

    promotionFlags :
      List NSKiriukhinOrbitStretchingPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open NSKiriukhinOrbitStretchingCarrierReceipt public

canonicalNSKiriukhinOrbitStretchingCarrierReceipt :
  NSKiriukhinOrbitStretchingCarrierReceipt
canonicalNSKiriukhinOrbitStretchingCarrierReceipt =
  record
    { status =
        orbitLevelCarrierRouteRecorded_modelOnly_noPromotion
    ; statusIsCanonical =
        refl
    ; carrierItems =
        canonicalNSKiriukhinOrbitStretchingCarrierItems
    ; carrierItemsAreCanonical =
        refl
    ; carrierScope =
        canonicalNSKiriukhinOrbitStretchingScope
    ; carrierScopeIsCanonical =
        refl
    ; openGaps =
        canonicalNSKiriukhinOrbitStretchingGaps
    ; openGapsAreCanonical =
        refl
    ; carrierMatrixNotation =
        "V_N"
    ; carrierMatrixNotationIsCanonical =
        refl
    ; orbitLevelSymmetricStretchingMatrix =
        true
    ; orbitLevelSymmetricStretchingMatrixIsTrue =
        refl
    ; candidateCarrierRecorded =
        true
    ; candidateCarrierRecordedIsTrue =
        refl
    ; symmetricStretchingMarked =
        true
    ; symmetricStretchingMarkedIsTrue =
        refl
    ; ensembleSpectralDecayModelOnlyFlag =
        true
    ; ensembleSpectralDecayModelOnlyFlagIsTrue =
        refl
    ; orbitContinuationCriterionExternalInput =
        true
    ; orbitContinuationCriterionExternalInputIsTrue =
        refl
    ; orbitContinuationCriterionModelLevel =
        true
    ; orbitContinuationCriterionModelLevelIsTrue =
        refl
    ; fullNSPromotionGateClosed =
        true
    ; fullNSPromotionGateClosedIsTrue =
        refl
    ; clayPromotionGateClosed =
        true
    ; clayPromotionGateClosedIsTrue =
        refl
    ; fullNSPromoted =
        false
    ; fullNSPromotedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; modelToFullNSContinuationGapOpen =
        true
    ; modelToFullNSContinuationGapOpenIsTrue =
        refl
    ; modelToClayPromotionGapOpen =
        true
    ; modelToClayPromotionGapOpenIsTrue =
        refl
    ; externalContinuationCriterionGapOpen =
        true
    ; externalContinuationCriterionGapOpenIsTrue =
        refl
    ; statement =
        nsKiriukhinOrbitStretchingCarrierStatement
    ; statementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "Candidate carrier: orbit-level symmetric stretching matrix V_N"
        ∷ "Ensemble spectral decay is model-only bookkeeping"
        ∷ "Orbit continuation criterion is external/model-level input"
        ∷ "Full NS promotion remains false"
        ∷ "Clay promotion remains false"
        ∷ []
    }

canonicalReceipt :
  NSKiriukhinOrbitStretchingCarrierReceipt
canonicalReceipt =
  canonicalNSKiriukhinOrbitStretchingCarrierReceipt
