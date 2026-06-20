module DASHI.Physics.Closure.NSPressurePoissonIdentityCorrectionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

------------------------------------------------------------------------
-- Corrected NS pressure-Poisson identity ledger.
--
-- This is a fail-closed correction surface: the legacy
-- `|omega|^2 / 4` pressure convention is recorded as superseded, and the
-- corrected identity is recorded as
--   -Δp = tr(S²) - |ω|²/2,
-- together with the claimed relations
--   Δp = 2 Q_vel
--   integral_{T^3} det(S) = -Pi/4
-- for the enstrophy-production proxy Pi.
--
-- No theorem promotion and no Clay promotion are discharged by this file.

data NSPressurePoissonIdentityCorrectionStatus : Set where
  pressurePoissonIdentityCorrectionRecorded :
    NSPressurePoissonIdentityCorrectionStatus

data NSPressurePoissonIdentityCorrectionStage : Set where
  legacyQuarterFactorRecordedAsHistoric :
    NSPressurePoissonIdentityCorrectionStage
  correctedPressureIdentityFromVelocityRecorded :
    NSPressurePoissonIdentityCorrectionStage
  strainFromRawVelocityReconstructionRecorded :
    NSPressurePoissonIdentityCorrectionStage
  qvelRelationRecorded :
    NSPressurePoissonIdentityCorrectionStage
  piProductionProxyRecorded :
    NSPressurePoissonIdentityCorrectionStage
  betchovDeterminantConsequenceRecorded :
    NSPressurePoissonIdentityCorrectionStage
  failClosedControlRecorded :
    NSPressurePoissonIdentityCorrectionStage
  theoremAuthorityKeptFalse :
    NSPressurePoissonIdentityCorrectionStage
  clayPromotionKeptFalse :
    NSPressurePoissonIdentityCorrectionStage

canonicalNSPressurePoissonIdentityCorrectionStages :
  List NSPressurePoissonIdentityCorrectionStage
canonicalNSPressurePoissonIdentityCorrectionStages =
  legacyQuarterFactorRecordedAsHistoric
  ∷ correctedPressureIdentityFromVelocityRecorded
  ∷ strainFromRawVelocityReconstructionRecorded
  ∷ qvelRelationRecorded
  ∷ piProductionProxyRecorded
  ∷ betchovDeterminantConsequenceRecorded
  ∷ failClosedControlRecorded
  ∷ theoremAuthorityKeptFalse
  ∷ clayPromotionKeptFalse
  ∷ []

data NSPressurePoissonIdentityCorrectionBlocker : Set where
  oldQuarterFactorNotForCurrentLane :
    NSPressurePoissonIdentityCorrectionBlocker
  velocityArchiveNeedsConventionBoundary :
    NSPressurePoissonIdentityCorrectionBlocker
  fullEnstrophyProductionControlNotClosed :
    NSPressurePoissonIdentityCorrectionBlocker
  theoremPromotionGateKeptClosed :
    NSPressurePoissonIdentityCorrectionBlocker
  clayPromotionGateKeptClosed :
    NSPressurePoissonIdentityCorrectionBlocker
  authorityBoundaryKeptClosed :
    NSPressurePoissonIdentityCorrectionBlocker

canonicalNSPressurePoissonIdentityCorrectionBlockers :
  List NSPressurePoissonIdentityCorrectionBlocker
canonicalNSPressurePoissonIdentityCorrectionBlockers =
  oldQuarterFactorNotForCurrentLane
  ∷ velocityArchiveNeedsConventionBoundary
  ∷ fullEnstrophyProductionControlNotClosed
  ∷ theoremPromotionGateKeptClosed
  ∷ clayPromotionGateKeptClosed
  ∷ authorityBoundaryKeptClosed
  ∷ []

data NSPressurePoissonIdentityCorrectionPromotion : Set where

nsPressurePoissonIdentityCorrectionPromotionImpossibleHere :
  NSPressurePoissonIdentityCorrectionPromotion →
  ⊥
nsPressurePoissonIdentityCorrectionPromotionImpossibleHere ()

data NSPressurePoissonIdentityCorrectionAuthority : Set where

canonicalCarrierText : String
canonicalCarrierText =
  "Raw Navier-Stokes velocity snapshots are the recorded source."

canonicalLegacyFormulaNoticeText : String
canonicalLegacyFormulaNoticeText =
  "The legacy factor |omega|^2 / 4 is recorded as a historic branch and is corrected here to |omega|^2 / 2 in the pressure-Poisson identity."

canonicalCorrectedPressureFormulaText : String
canonicalCorrectedPressureFormulaText =
  "-Delta p = tr(S^2) - |omega|^2/2."

canonicalQvelRelationText : String
canonicalQvelRelationText =
  "Delta p = 2 Qvel is recorded as the correction-compatible form."

canonicalPiProxyText : String
canonicalPiProxyText =
  "Pi is recorded as the enstrophy-production proxy Pi := ω_i S_ij ω_j."

canonicalDeterminantRelationText : String
canonicalDeterminantRelationText =
  "Combined target relation is recorded as integral_{T^3} det(S) = -Pi/4."

canonicalCorrectionBoundaryText : String
canonicalCorrectionBoundaryText =
  "This fail-closed correction ledger explicitly deprecates the old /4 term, records the corrected |omega|^2/2 formula from raw velocity snapshots, and records the target correction targets (Pi and integral det(S))."

canonicalOText : String
canonicalOText =
  "O: Start from the raw velocity-snapshot pressure archive and record the correction target on the same carrier."

canonicalRText : String
canonicalRText =
  "R: Record legacy-to-correct factor migration: legacy |omega|^2/4 is superseded by the corrected |omega|^2/2 formula."

canonicalCText : String
canonicalCText =
  "C: Record the three targets: corrected pressure Poisson identity, Δp = 2 Qvel, and integral det(S) = -Pi/4."

canonicalSText : String
canonicalSText =
  "S: Strain reconstruction and Pi-proxy audit are recorded from raw snapshots; authority and promotion remains closed."

canonicalLText : String
canonicalLText =
  "L: Local correction surface only; no global analytic theorem is promoted."

canonicalPText : String
canonicalPText =
  "P: No theorem promotion, no theorem authority, and no Clay promotion are emitted by this receipt."

canonicalGText : String
canonicalGText =
  "G: Keep authority boundaries explicit and closed; no Clay crossing occurs on this correction lane."

canonicalFText : String
canonicalFText =
  "F: Remaining gaps: full enstrophy-production quantitative control and any downstream global use remain open."

record NSPressurePoissonIdentityCorrectionORCSLPGF : Set where
  constructor mkNSPressurePoissonIdentityCorrectionORCSLPGF
  field
    O : String
    R : String
    C : String
    S : String
    L : String
    P : String
    G : String
    F : String

canonicalNSPressurePoissonIdentityCorrectionORCSLPGF :
  NSPressurePoissonIdentityCorrectionORCSLPGF
canonicalNSPressurePoissonIdentityCorrectionORCSLPGF =
  mkNSPressurePoissonIdentityCorrectionORCSLPGF
    canonicalOText
    canonicalRText
    canonicalCText
    canonicalSText
    canonicalLText
    canonicalPText
    canonicalGText
    canonicalFText

canonicalReceiptBoundary : List String
canonicalReceiptBoundary =
  "Raw velocity-snapshot carrier recorded."
  ∷ canonicalLegacyFormulaNoticeText
  ∷ canonicalCorrectedPressureFormulaText
  ∷ canonicalQvelRelationText
  ∷ canonicalPiProxyText
  ∷ canonicalDeterminantRelationText
  ∷ "Legacy factor /4 formula is treated as an explicit superseded branch."
  ∷ "Theorem authority, calculation authority, and Clay promotion remain false."
  ∷ []

record NSPressurePoissonIdentityCorrectionReceipt : Setω where
  field
    status :
      NSPressurePoissonIdentityCorrectionStatus
    statusIsCanonical :
      status ≡ pressurePoissonIdentityCorrectionRecorded

    stageTrail :
      List NSPressurePoissonIdentityCorrectionStage
    stageTrailIsCanonical :
      stageTrail ≡ canonicalNSPressurePoissonIdentityCorrectionStages
    stageCount :
      Nat
    stageCountIsCanonical :
      stageCount ≡ listLength canonicalNSPressurePoissonIdentityCorrectionStages

    blockerTrail :
      List NSPressurePoissonIdentityCorrectionBlocker
    blockerTrailIsCanonical :
      blockerTrail ≡ canonicalNSPressurePoissonIdentityCorrectionBlockers
    blockerCount :
      Nat
    blockerCountIsCanonical :
      blockerCount ≡ listLength canonicalNSPressurePoissonIdentityCorrectionBlockers

    controlCard :
      NSPressurePoissonIdentityCorrectionORCSLPGF
    controlCardIsCanonical :
      controlCard ≡ canonicalNSPressurePoissonIdentityCorrectionORCSLPGF

    carrierText :
      String
    carrierTextIsCanonical :
      carrierText ≡ canonicalCarrierText

    legacyFormulaNoticeText :
      String
    legacyFormulaNoticeTextIsCanonical :
      legacyFormulaNoticeText ≡ canonicalLegacyFormulaNoticeText

    correctedPressureFormulaText :
      String
    correctedPressureFormulaTextIsCanonical :
      correctedPressureFormulaText ≡ canonicalCorrectedPressureFormulaText

    qvelRelationText :
      String
    qvelRelationTextIsCanonical :
      qvelRelationText ≡ canonicalQvelRelationText

    piProxyText :
      String
    piProxyTextIsCanonical :
      piProxyText ≡ canonicalPiProxyText

    determinantRelationText :
      String
    determinantRelationTextIsCanonical :
      determinantRelationText ≡ canonicalDeterminantRelationText

    correctionBoundary :
      String
    correctionBoundaryIsCanonical :
      correctionBoundary ≡ canonicalCorrectionBoundaryText

    receiptBoundary :
      List String
    receiptBoundaryIsCanonical :
      receiptBoundary ≡ canonicalReceiptBoundary

    legacyQuarterFactorMarkedHistoric :
      Bool
    legacyQuarterFactorMarkedHistoricIsTrue :
      legacyQuarterFactorMarkedHistoric ≡ true

    correctedPressureFormulaRecorded :
      Bool
    correctedPressureFormulaRecordedIsTrue :
      correctedPressureFormulaRecorded ≡ true

    strainReconstructionRecorded :
      Bool
    strainReconstructionRecordedIsTrue :
      strainReconstructionRecorded ≡ true

    qvelRelationRecordedFlag :
      Bool
    qvelRelationRecordedFlagIsTrue :
      qvelRelationRecordedFlag ≡ true

    betchovConsequenceRecorded :
      Bool
    betchovConsequenceRecordedIsTrue :
      betchovConsequenceRecorded ≡ true

    theoremAuthority :
      Bool
    theoremAuthorityIsFalse :
      theoremAuthority ≡ false

    calculationAuthority :
      Bool
    calculationAuthorityIsFalse :
      calculationAuthority ≡ false

    clayPromotion :
      Bool
    clayPromotionIsFalse :
      clayPromotion ≡ false

    terminalClayPromotion :
      Bool
    terminalClayPromotionIsFalse :
      terminalClayPromotion ≡ false

    promotionFlags :
      List NSPressurePoissonIdentityCorrectionPromotion
    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    authorityTrail :
      List NSPressurePoissonIdentityCorrectionAuthority
    authorityTrailIsCanonical :
      authorityTrail ≡ []

open NSPressurePoissonIdentityCorrectionReceipt public

canonicalNSPressurePoissonIdentityCorrectionReceipt :
  NSPressurePoissonIdentityCorrectionReceipt
canonicalNSPressurePoissonIdentityCorrectionReceipt =
  record
    { status =
        pressurePoissonIdentityCorrectionRecorded
    ; statusIsCanonical =
        refl
    ; stageTrail =
        canonicalNSPressurePoissonIdentityCorrectionStages
    ; stageTrailIsCanonical =
        refl
    ; stageCount =
        listLength canonicalNSPressurePoissonIdentityCorrectionStages
    ; stageCountIsCanonical =
        refl
    ; blockerTrail =
        canonicalNSPressurePoissonIdentityCorrectionBlockers
    ; blockerTrailIsCanonical =
        refl
    ; blockerCount =
        listLength canonicalNSPressurePoissonIdentityCorrectionBlockers
    ; blockerCountIsCanonical =
        refl
    ; controlCard =
        canonicalNSPressurePoissonIdentityCorrectionORCSLPGF
    ; controlCardIsCanonical =
        refl
    ; carrierText =
        canonicalCarrierText
    ; carrierTextIsCanonical =
        refl
    ; legacyFormulaNoticeText =
        canonicalLegacyFormulaNoticeText
    ; legacyFormulaNoticeTextIsCanonical =
        refl
    ; correctedPressureFormulaText =
        canonicalCorrectedPressureFormulaText
    ; correctedPressureFormulaTextIsCanonical =
        refl
    ; qvelRelationText =
        canonicalQvelRelationText
    ; qvelRelationTextIsCanonical =
        refl
    ; piProxyText =
        canonicalPiProxyText
    ; piProxyTextIsCanonical =
        refl
    ; determinantRelationText =
        canonicalDeterminantRelationText
    ; determinantRelationTextIsCanonical =
        refl
    ; correctionBoundary =
        canonicalCorrectionBoundaryText
    ; correctionBoundaryIsCanonical =
        refl
    ; receiptBoundary =
        canonicalReceiptBoundary
    ; receiptBoundaryIsCanonical =
        refl
    ; legacyQuarterFactorMarkedHistoric =
        true
    ; legacyQuarterFactorMarkedHistoricIsTrue =
        refl
    ; correctedPressureFormulaRecorded =
        true
    ; correctedPressureFormulaRecordedIsTrue =
        refl
    ; strainReconstructionRecorded =
        true
    ; strainReconstructionRecordedIsTrue =
        refl
    ; qvelRelationRecordedFlag =
        true
    ; qvelRelationRecordedFlagIsTrue =
        refl
    ; betchovConsequenceRecorded =
        true
    ; betchovConsequenceRecordedIsTrue =
        refl
    ; theoremAuthority =
        false
    ; theoremAuthorityIsFalse =
        refl
    ; calculationAuthority =
        false
    ; calculationAuthorityIsFalse =
        refl
    ; clayPromotion =
        false
    ; clayPromotionIsFalse =
        refl
    ; terminalClayPromotion =
        false
    ; terminalClayPromotionIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; authorityTrail =
        []
    ; authorityTrailIsCanonical =
        refl
    }
