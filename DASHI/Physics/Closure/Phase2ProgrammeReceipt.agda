module DASHI.Physics.Closure.Phase2ProgrammeReceipt where

open import Agda.Primitive using (Set; Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.ClayNSCurrentStateReceipt as Current

data Phase2ProgrammeStatus : Set where
  phase2ProgrammeRecordedWithoutClayPromotion :
    Phase2ProgrammeStatus

data Phase2ProgrammeWorkItem : Set where
  runYMKToInfinityTightness :
    Phase2ProgrammeWorkItem

  preserveLerayWeakSolutionBranch :
    Phase2ProgrammeWorkItem

  proveCriticalBesovEstimate :
    Phase2ProgrammeWorkItem

  deriveCKMYukawaNormalisation :
    Phase2ProgrammeWorkItem

  completePaper8GaugeSections :
    Phase2ProgrammeWorkItem

  constructUniformEnstrophyPassage :
    Phase2ProgrammeWorkItem
  constructUniformVorticityControl :
    Phase2ProgrammeWorkItem
  constructCriticalBesovControl :
    Phase2ProgrammeWorkItem
  dischargeContinuumBKMAuthority :
    Phase2ProgrammeWorkItem
  seekGlobalSmoothRegularityOnlyAfterBKM :
    Phase2ProgrammeWorkItem

canonicalPhase2ProgrammeWorkItems :
  List Phase2ProgrammeWorkItem
canonicalPhase2ProgrammeWorkItems =
  runYMKToInfinityTightness
  ∷ preserveLerayWeakSolutionBranch
  ∷ proveCriticalBesovEstimate
  ∷ deriveCKMYukawaNormalisation
  ∷ completePaper8GaugeSections
  ∷ constructUniformEnstrophyPassage
  ∷ constructUniformVorticityControl
  ∷ constructCriticalBesovControl
  ∷ dischargeContinuumBKMAuthority
  ∷ seekGlobalSmoothRegularityOnlyAfterBKM
  ∷ []

phase2ProgrammeStatement : String
phase2ProgrammeStatement =
  "Phase 2 targets YM k-to-infinity tightness, NS critical Besov/vorticity control, CKM Yukawa normalisation, and Paper 8 gauge-section completion without Clay, exact SM, or terminal promotion."

record Phase2ProgrammeReceipt : Setω where
  field
    status :
      Phase2ProgrammeStatus

    currentStateReceipt :
      Current.ClayNSCurrentStateReceipt

    currentWeakBranchTrue :
      Current.lerayWeakSolutionBranchAvailable
        currentStateReceipt
      ≡
      true

    currentBKMVorticityFalse :
      Current.uniformBKMVorticityControlClosed
        currentStateReceipt
      ≡
      false

    currentSmoothRegularityFalse :
      Current.globalSmoothRegularityProved currentStateReceipt ≡ false

    currentClayFalse :
      Current.clayNavierStokesPromoted currentStateReceipt ≡ false

    workItems :
      List Phase2ProgrammeWorkItem

    workItemsAreCanonical :
      workItems ≡ canonicalPhase2ProgrammeWorkItems

    phase2ProgrammeRecorded :
      Bool

    phase2ProgrammeRecordedIsTrue :
      phase2ProgrammeRecorded ≡ true

    lerayWeakSolutionBranchAvailable :
      Bool

    lerayWeakSolutionBranchAvailableIsTrue :
      lerayWeakSolutionBranchAvailable ≡ true

    ymKToInfinityTightnessConstructed :
      Bool

    ymKToInfinityTightnessConstructedIsFalse :
      ymKToInfinityTightnessConstructed ≡ false

    ckmYukawaNormalisationDerived :
      Bool

    ckmYukawaNormalisationDerivedIsFalse :
      ckmYukawaNormalisationDerived ≡ false

    paper8GaugeSectionsCompleted :
      Bool

    paper8GaugeSectionsCompletedIsFalse :
      paper8GaugeSectionsCompleted ≡ false

    uniformEnstrophyPassageConstructed :
      Bool

    uniformEnstrophyPassageConstructedIsFalse :
      uniformEnstrophyPassageConstructed ≡ false

    uniformVorticityControlConstructed :
      Bool

    uniformVorticityControlConstructedIsFalse :
      uniformVorticityControlConstructed ≡ false

    criticalBesovControlConstructed :
      Bool

    criticalBesovControlConstructedIsFalse :
      criticalBesovControlConstructed ≡ false

    continuumBKMContinuationDischarged :
      Bool

    continuumBKMContinuationDischargedIsFalse :
      continuumBKMContinuationDischarged ≡ false

    globalSmoothRegularityProved :
      Bool

    globalSmoothRegularityProvedIsFalse :
      globalSmoothRegularityProved ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    exactStandardModelPromoted :
      Bool

    exactStandardModelPromotedIsFalse :
      exactStandardModelPromoted ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ phase2ProgrammeStatement

    receiptBoundary :
      List String

open Phase2ProgrammeReceipt public

canonicalPhase2ProgrammeReceipt :
  Phase2ProgrammeReceipt
canonicalPhase2ProgrammeReceipt =
  record
    { status =
        phase2ProgrammeRecordedWithoutClayPromotion
    ; currentStateReceipt =
        Current.canonicalClayNSCurrentStateReceipt
    ; currentWeakBranchTrue =
        refl
    ; currentBKMVorticityFalse =
        refl
    ; currentSmoothRegularityFalse =
        refl
    ; currentClayFalse =
        refl
    ; workItems =
        canonicalPhase2ProgrammeWorkItems
    ; workItemsAreCanonical =
        refl
    ; phase2ProgrammeRecorded =
        true
    ; phase2ProgrammeRecordedIsTrue =
        refl
    ; lerayWeakSolutionBranchAvailable =
        true
    ; lerayWeakSolutionBranchAvailableIsTrue =
        refl
    ; ymKToInfinityTightnessConstructed =
        false
    ; ymKToInfinityTightnessConstructedIsFalse =
        refl
    ; ckmYukawaNormalisationDerived =
        false
    ; ckmYukawaNormalisationDerivedIsFalse =
        refl
    ; paper8GaugeSectionsCompleted =
        false
    ; paper8GaugeSectionsCompletedIsFalse =
        refl
    ; uniformEnstrophyPassageConstructed =
        false
    ; uniformEnstrophyPassageConstructedIsFalse =
        refl
    ; uniformVorticityControlConstructed =
        false
    ; uniformVorticityControlConstructedIsFalse =
        refl
    ; criticalBesovControlConstructed =
        false
    ; criticalBesovControlConstructedIsFalse =
        refl
    ; continuumBKMContinuationDischarged =
        false
    ; continuumBKMContinuationDischargedIsFalse =
        refl
    ; globalSmoothRegularityProved =
        false
    ; globalSmoothRegularityProvedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; exactStandardModelPromoted =
        false
    ; exactStandardModelPromotedIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; statement =
        phase2ProgrammeStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        "Phase 2 is a programme receipt, not a completed regularity theorem"
        ∷ "YM k-to-infinity tightness, CKM Yukawa normalisation, and Paper 8 gauge sections are named targets"
        ∷ "The Leray weak-solution branch remains true while critical Besov/vorticity control is open"
        ∷ "Uniform enstrophy, continuum BKM, global smoothness, exact SM, Clay, and terminal promotion remain false"
        ∷ []
    }

phase2ProgrammeKeepsClayFalse :
  clayNavierStokesPromoted canonicalPhase2ProgrammeReceipt ≡ false
phase2ProgrammeKeepsClayFalse =
  refl
