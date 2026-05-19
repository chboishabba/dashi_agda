module DASHI.Physics.Closure.W4StrictPhysicalScaleSettingLaneObligation where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.ChemistryPhysicalHandoffDiagnostic as Handoff
import DASHI.Physics.Closure.ChemistryStrictPhysicalSemanticsBlocker as Blocker
import DASHI.Physics.Closure.W4StrictPhysicalNextObligation as Next
import DASHI.Physics.Closure.W4StrictPhysicalObligationLedger as Ledger

------------------------------------------------------------------------
-- W4i Candidate256 scale-setting lane obligation.
--
-- This module narrows the first strict-physical lane to scale-setting only.
-- It records the exact carrier/map/law surface a later worker must inhabit,
-- while preserving the ledger boundary that spectra, bonding, empirical
-- validation, and physical closure remain separate obligations.

record Candidate256ScaleSettingLaneFields : Setω where
  field
    physicalScaleCarrier : Set

    quotientClassScaleMap :
      Handoff.QuotientCarrier Next.canonicalCandidate256QuotientLaw →
      physicalScaleCarrier

    LchemScalePreservationLaw :
      Handoff.QuotientLawAtWitness Next.canonicalCandidate256QuotientLaw →
      Set

Candidate256ScaleSettingLawStillNeeded :
  Candidate256ScaleSettingLaneFields →
  Set₁
Candidate256ScaleSettingLawStillNeeded fields =
  (law :
    Handoff.QuotientLawAtWitness Next.canonicalCandidate256QuotientLaw) →
  Candidate256ScaleSettingLaneFields.LchemScalePreservationLaw fields law

data Candidate256ScaleSettingLaneStatus : Set where
  scaleSettingObligationNeeded :
    Next.W4StrictPhysicalBoundaryToken →
    Ledger.Candidate256StrictPhysicalLedgerStatus Ledger.scaleSettingLane →
    Candidate256ScaleSettingLaneStatus

record Candidate256ScaleSettingLaneObligationReceipt : Setω where
  field
    ledger : Ledger.Candidate256StrictPhysicalAllNeededLedger
    scaleSettingEntry : Ledger.Candidate256StrictPhysicalChecklistEntry

    recommendedLane :
      Ledger.Candidate256StrictPhysicalLane

    recommendedLaneIsScaleSetting :
      recommendedLane ≡ Ledger.scaleSettingLane

    missingIngredient :
      Blocker.StrictPhysicalMissingIngredient

    missingIngredientIsScaleSetting :
      missingIngredient ≡ Blocker.missingScaleSettingLaw

    requiredPhysicalScaleCarrier : String
    requiredQuotientClassScaleMap : String
    requiredLchemPreservationLaw : String

    scaleSettingFieldsNeeded :
      Candidate256ScaleSettingLaneFields →
      Set₁

    obligationStatus : Candidate256ScaleSettingLaneStatus
    obligationNeededToken : Next.W4StrictPhysicalBoundaryToken

    downstreamStillMissing :
      List Blocker.StrictPhysicalMissingIngredient

    downstreamBoundary :
      List String

    noScaleSettingLawInhabitedHere :
      List String

canonicalCandidate256ScaleSettingLaneObligationReceipt :
  Candidate256ScaleSettingLaneObligationReceipt
canonicalCandidate256ScaleSettingLaneObligationReceipt =
  record
    { ledger =
        Ledger.canonicalCandidate256StrictPhysicalAllNeededLedger
    ; scaleSettingEntry =
        Ledger.scaleSettingEntry
    ; recommendedLane =
        Ledger.candidate256RecommendedNextLane
    ; recommendedLaneIsScaleSetting =
        refl
    ; missingIngredient =
        Ledger.candidate256RecommendedNextMissingIngredient
    ; missingIngredientIsScaleSetting =
        refl
    ; requiredPhysicalScaleCarrier =
        "provide a physical scale carrier for Candidate256 quotient classes"
    ; requiredQuotientClassScaleMap =
        "map each Candidate256 quotient class into the physical scale carrier"
    ; requiredLchemPreservationLaw =
        "state and later inhabit an L_chem preservation law at the Candidate256 left/right witness"
    ; scaleSettingFieldsNeeded =
        Candidate256ScaleSettingLawStillNeeded
    ; obligationStatus =
        scaleSettingObligationNeeded
          Next.canonicalCandidate256StrictPhysicalBoundaryToken
          (Ledger.laneStatus Ledger.scaleSettingLane)
    ; obligationNeededToken =
        Next.canonicalCandidate256StrictPhysicalBoundaryToken
    ; downstreamStillMissing =
        Blocker.missingSpectralObservableMap
        ∷ Blocker.missingBondingInterpretation
        ∷ Blocker.missingEmpiricalPhysicalValidation
        ∷ []
    ; downstreamBoundary =
        "After scale-setting, spectral observable mapping remains a separate strict-physical lane"
        ∷ "After scale-setting, bonding interpretation remains a separate strict-physical lane"
        ∷ "After scale-setting, empirical physical validation remains a separate strict-physical lane"
        ∷ []
    ; noScaleSettingLawInhabitedHere =
        "This module exposes the Candidate256 scale-setting obligation surface only"
        ∷ "It does not inhabit Candidate256ScaleSettingLawStillNeeded"
        ∷ "It does not build StrictPhysicalBoundaryPreservation or a strict physical consumer"
        ∷ "It makes no spectra, bonding, validation, or physical-closure claim"
        ∷ []
    }

candidate256ScaleSettingFieldsNeeded :
  Candidate256ScaleSettingLaneFields →
  Set₁
candidate256ScaleSettingFieldsNeeded =
  Candidate256ScaleSettingLaneObligationReceipt.scaleSettingFieldsNeeded
    canonicalCandidate256ScaleSettingLaneObligationReceipt

candidate256ScaleSettingObligationStatus :
  Candidate256ScaleSettingLaneStatus
candidate256ScaleSettingObligationStatus =
  Candidate256ScaleSettingLaneObligationReceipt.obligationStatus
    canonicalCandidate256ScaleSettingLaneObligationReceipt

candidate256ScaleSettingDownstreamStillMissing :
  List Blocker.StrictPhysicalMissingIngredient
candidate256ScaleSettingDownstreamStillMissing =
  Candidate256ScaleSettingLaneObligationReceipt.downstreamStillMissing
    canonicalCandidate256ScaleSettingLaneObligationReceipt
