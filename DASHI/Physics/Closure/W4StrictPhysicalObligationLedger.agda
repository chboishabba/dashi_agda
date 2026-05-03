module DASHI.Physics.Closure.W4StrictPhysicalObligationLedger where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.ChemistryStrictPhysicalSemanticsBlocker as Blocker
import DASHI.Physics.Closure.W4StrictPhysicalNextObligation as Next

------------------------------------------------------------------------
-- W4h strict-physical obligation checklist/ledger.
--
-- This module is governance only.  It orders the strict physical ingredients
-- that Candidate256 still needs before any scale-setting, spectra, bonding,
-- empirical-validation, or physical-closure claim can be consumed.

data Empty : Set where

data Candidate256StrictPhysicalLane : Set where
  scaleSettingLane : Candidate256StrictPhysicalLane
  spectralObservableLane : Candidate256StrictPhysicalLane
  bondingInterpretationLane : Candidate256StrictPhysicalLane
  empiricalPhysicalValidationLane : Candidate256StrictPhysicalLane

data Candidate256StrictPhysicalIngredientInhabited :
  Candidate256StrictPhysicalLane → Set where

data Candidate256StrictPhysicalLedgerStatus
  (lane : Candidate256StrictPhysicalLane) :
  Set where
  obligationNeededUninhabitedHere :
    (Candidate256StrictPhysicalIngredientInhabited lane -> Empty) ->
    Candidate256StrictPhysicalLedgerStatus lane

laneOrder : Candidate256StrictPhysicalLane → Nat
laneOrder scaleSettingLane = 1
laneOrder spectralObservableLane = 2
laneOrder bondingInterpretationLane = 3
laneOrder empiricalPhysicalValidationLane = 4

laneMissingIngredient :
  Candidate256StrictPhysicalLane →
  Blocker.StrictPhysicalMissingIngredient
laneMissingIngredient scaleSettingLane =
  Blocker.missingScaleSettingLaw
laneMissingIngredient spectralObservableLane =
  Blocker.missingSpectralObservableMap
laneMissingIngredient bondingInterpretationLane =
  Blocker.missingBondingInterpretation
laneMissingIngredient empiricalPhysicalValidationLane =
  Blocker.missingEmpiricalPhysicalValidation

laneRequirement : Candidate256StrictPhysicalLane → String
laneRequirement scaleSettingLane =
  Next.Candidate256StrictPhysicalNextObligationReceipt.requiredScaleSettingLaw
    Next.canonicalCandidate256StrictPhysicalNextObligationReceipt
laneRequirement spectralObservableLane =
  Next.Candidate256StrictPhysicalNextObligationReceipt.requiredSpectralObservableMap
    Next.canonicalCandidate256StrictPhysicalNextObligationReceipt
laneRequirement bondingInterpretationLane =
  Next.Candidate256StrictPhysicalNextObligationReceipt.requiredBondingInterpretation
    Next.canonicalCandidate256StrictPhysicalNextObligationReceipt
laneRequirement empiricalPhysicalValidationLane =
  Next.Candidate256StrictPhysicalNextObligationReceipt.requiredEmpiricalPhysicalValidation
    Next.canonicalCandidate256StrictPhysicalNextObligationReceipt

laneStatus :
  (lane : Candidate256StrictPhysicalLane) →
  Candidate256StrictPhysicalLedgerStatus lane
laneStatus lane = obligationNeededUninhabitedHere λ ()

record Candidate256StrictPhysicalChecklistEntry : Set where
  field
    order : Nat
    lane : Candidate256StrictPhysicalLane
    missingIngredient : Blocker.StrictPhysicalMissingIngredient
    requirement : String
    status : Candidate256StrictPhysicalLedgerStatus lane
    boundaryToken : Next.W4StrictPhysicalBoundaryToken

mkEntry :
  (lane : Candidate256StrictPhysicalLane) →
  Candidate256StrictPhysicalChecklistEntry
mkEntry lane =
  record
    { order = laneOrder lane
    ; lane = lane
    ; missingIngredient = laneMissingIngredient lane
    ; requirement = laneRequirement lane
    ; status = laneStatus lane
    ; boundaryToken = Next.canonicalCandidate256StrictPhysicalBoundaryToken
    }

scaleSettingEntry : Candidate256StrictPhysicalChecklistEntry
scaleSettingEntry = mkEntry scaleSettingLane

spectralObservableEntry : Candidate256StrictPhysicalChecklistEntry
spectralObservableEntry = mkEntry spectralObservableLane

bondingInterpretationEntry : Candidate256StrictPhysicalChecklistEntry
bondingInterpretationEntry = mkEntry bondingInterpretationLane

empiricalPhysicalValidationEntry : Candidate256StrictPhysicalChecklistEntry
empiricalPhysicalValidationEntry = mkEntry empiricalPhysicalValidationLane

candidate256StrictPhysicalOrderedChecklist :
  List Candidate256StrictPhysicalChecklistEntry
candidate256StrictPhysicalOrderedChecklist =
  scaleSettingEntry
  ∷ spectralObservableEntry
  ∷ bondingInterpretationEntry
  ∷ empiricalPhysicalValidationEntry
  ∷ []

record Candidate256StrictPhysicalAllNeededLedger : Setω where
  field
    blocker :
      Blocker.ChemistryStrictPhysicalSemanticsBlocker
        Next.canonicalCandidate256AcceptedRetargetedCarrier
        Next.canonicalCandidate256QuotientLaw

    receipt : Next.Candidate256StrictPhysicalNextObligationReceipt

    scaleSettingNeeded : Candidate256StrictPhysicalChecklistEntry
    spectralObservableNeeded : Candidate256StrictPhysicalChecklistEntry
    bondingInterpretationNeeded : Candidate256StrictPhysicalChecklistEntry
    empiricalPhysicalValidationNeeded : Candidate256StrictPhysicalChecklistEntry

    orderedChecklist : List Candidate256StrictPhysicalChecklistEntry
    recommendedNextLane : Candidate256StrictPhysicalLane
    recommendedNextMissingIngredient :
      Blocker.StrictPhysicalMissingIngredient

    obligationsNeededBoundary : List String
    noPhysicalClosureClaim : Next.W4StrictPhysicalBoundaryToken

canonicalCandidate256StrictPhysicalAllNeededLedger :
  Candidate256StrictPhysicalAllNeededLedger
canonicalCandidate256StrictPhysicalAllNeededLedger =
  record
    { blocker =
        Blocker.canonicalCandidate256StrictPhysicalSemanticsBlocker
    ; receipt =
        Next.canonicalCandidate256StrictPhysicalNextObligationReceipt
    ; scaleSettingNeeded = scaleSettingEntry
    ; spectralObservableNeeded = spectralObservableEntry
    ; bondingInterpretationNeeded = bondingInterpretationEntry
    ; empiricalPhysicalValidationNeeded = empiricalPhysicalValidationEntry
    ; orderedChecklist = candidate256StrictPhysicalOrderedChecklist
    ; recommendedNextLane = scaleSettingLane
    ; recommendedNextMissingIngredient =
        Blocker.canonicalCandidate256StrictPhysicalSemanticsNextMissingIngredient
    ; obligationsNeededBoundary =
        "Candidate256 strict physical work remains obligations-needed, not closure"
        ∷ "Scale-setting is ordered first because the current blocker exposes it as the next missing ingredient"
        ∷ "Spectral observable, bonding interpretation, and empirical physical validation remain separately needed"
        ∷ "No physical theorem promotion is constructed by this ledger"
        ∷ []
    ; noPhysicalClosureClaim =
        Next.canonicalCandidate256StrictPhysicalBoundaryToken
    }

candidate256RecommendedNextLane : Candidate256StrictPhysicalLane
candidate256RecommendedNextLane =
  Candidate256StrictPhysicalAllNeededLedger.recommendedNextLane
    canonicalCandidate256StrictPhysicalAllNeededLedger

candidate256RecommendedNextMissingIngredient :
  Blocker.StrictPhysicalMissingIngredient
candidate256RecommendedNextMissingIngredient =
  Candidate256StrictPhysicalAllNeededLedger.recommendedNextMissingIngredient
    canonicalCandidate256StrictPhysicalAllNeededLedger
