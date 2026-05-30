module DASHI.Physics.Closure.Phase2ProgrammeReceipt where

open import Agda.Primitive using (Set; Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
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

------------------------------------------------------------------------
-- Manager C clay-reframe governance tranche.

data ManagerCReframePriority : Set where
  papersSixAndEightFirst : ManagerCReframePriority
  ymProductLatticeSecond : ManagerCReframePriority
  smGaugeDerivationThird : ManagerCReframePriority
  ckmCompletionFourth : ManagerCReframePriority
  nsClayParkedFifth : ManagerCReframePriority

canonicalManagerCReframePriorities :
  List ManagerCReframePriority
canonicalManagerCReframePriorities =
  papersSixAndEightFirst
  ∷ ymProductLatticeSecond
  ∷ smGaugeDerivationThird
  ∷ ckmCompletionFourth
  ∷ nsClayParkedFifth
  ∷ []

data ManagerCExternalInput : Set where
  nsUniformVorticityDirectionControl : ManagerCExternalInput
  ymNonperturbativeClusterExpansion : ManagerCExternalInput
  ckmCPFromComplexCMPeriodRatio : ManagerCExternalInput

canonicalManagerCExternalInputs :
  List ManagerCExternalInput
canonicalManagerCExternalInputs =
  nsUniformVorticityDirectionControl
  ∷ ymNonperturbativeClusterExpansion
  ∷ ckmCPFromComplexCMPeriodRatio
  ∷ []

data ManagerCReframePromotion : Set where

managerCReframePromotionImpossibleHere :
  ManagerCReframePromotion → ⊥
managerCReframePromotionImpossibleHere ()

managerCClayReframeCommitMessage : String
managerCClayReframeCommitMessage =
  "YM reframed: 1+1D carrier is trivially confining; 4D product lattice + Balaban authority is the correct Clay YM path. NS stopped at Leray ceiling. Programme priorities reordered: Papers 6/8 first, then YM product lattice, then SM gauge group, then CKM CP mechanism, then NS Clay parked."

managerCClayReframeTagName : String
managerCClayReframeTagName =
  "phase2-clay-reframed-v1"

record ManagerCClayReframeReceipt : Setω where
  field
    phase2Receipt : Phase2ProgrammeReceipt
    phase2TerminalFalse :
      terminalClaimPromoted phase2Receipt ≡ false
    phase2NSClayFalse :
      clayNavierStokesPromoted phase2Receipt ≡ false
    naturalCarrierYMIs1p1D : Bool
    naturalCarrierYMIs1p1DIsTrue :
      naturalCarrierYMIs1p1D ≡ true
    naturalCarrierIsClayYMTarget : Bool
    naturalCarrierIsClayYMTargetIsFalse :
      naturalCarrierIsClayYMTarget ≡ false
    productLatticeBalabanRouteRecorded : Bool
    productLatticeBalabanRouteRecordedIsTrue :
      productLatticeBalabanRouteRecorded ≡ true
    productLatticeUniversalityClassSettled : Bool
    productLatticeUniversalityClassSettledIsFalse :
      productLatticeUniversalityClassSettled ≡ false
    vacuumUniquenessSettled : Bool
    vacuumUniquenessSettledIsFalse :
      vacuumUniquenessSettled ≡ false
    nsStoppedAtLerayCeiling : Bool
    nsStoppedAtLerayCeilingIsTrue :
      nsStoppedAtLerayCeiling ≡ true
    assignFurtherNSClayWorkers : Bool
    assignFurtherNSClayWorkersIsFalse :
      assignFurtherNSClayWorkers ≡ false
    priorities : List ManagerCReframePriority
    prioritiesAreCanonical :
      priorities ≡ canonicalManagerCReframePriorities
    externalInputs : List ManagerCExternalInput
    externalInputsAreCanonical :
      externalInputs ≡ canonicalManagerCExternalInputs
    cpFromComplexCMPeriodRatioCandidate : Bool
    cpFromComplexCMPeriodRatioCandidateIsTrue :
      cpFromComplexCMPeriodRatioCandidate ≡ true
    commitMessage : String
    commitMessageIsCanonical :
      commitMessage ≡ managerCClayReframeCommitMessage
    tagName : String
    tagNameIsCanonical :
      tagName ≡ managerCClayReframeTagName
    clayYangMillsPromoted : Bool
    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false
    clayNavierStokesPromoted : Bool
    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false
    ckmFinalPromoted : Bool
    ckmFinalPromotedIsFalse :
      ckmFinalPromoted ≡ false
    exactStandardModelPromoted : Bool
    exactStandardModelPromotedIsFalse :
      exactStandardModelPromoted ≡ false
    terminalClaimPromoted : Bool
    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false
    promotionFlags : List ManagerCReframePromotion
    promotionFlagsAreEmpty :
      promotionFlags ≡ []

open ManagerCClayReframeReceipt public

canonicalManagerCClayReframeReceipt :
  ManagerCClayReframeReceipt
canonicalManagerCClayReframeReceipt =
  record
    { phase2Receipt = canonicalPhase2ProgrammeReceipt
    ; phase2TerminalFalse = refl
    ; phase2NSClayFalse = refl
    ; naturalCarrierYMIs1p1D = true
    ; naturalCarrierYMIs1p1DIsTrue = refl
    ; naturalCarrierIsClayYMTarget = false
    ; naturalCarrierIsClayYMTargetIsFalse = refl
    ; productLatticeBalabanRouteRecorded = true
    ; productLatticeBalabanRouteRecordedIsTrue = refl
    ; productLatticeUniversalityClassSettled = false
    ; productLatticeUniversalityClassSettledIsFalse = refl
    ; vacuumUniquenessSettled = false
    ; vacuumUniquenessSettledIsFalse = refl
    ; nsStoppedAtLerayCeiling = true
    ; nsStoppedAtLerayCeilingIsTrue = refl
    ; assignFurtherNSClayWorkers = false
    ; assignFurtherNSClayWorkersIsFalse = refl
    ; priorities = canonicalManagerCReframePriorities
    ; prioritiesAreCanonical = refl
    ; externalInputs = canonicalManagerCExternalInputs
    ; externalInputsAreCanonical = refl
    ; cpFromComplexCMPeriodRatioCandidate = true
    ; cpFromComplexCMPeriodRatioCandidateIsTrue = refl
    ; commitMessage = managerCClayReframeCommitMessage
    ; commitMessageIsCanonical = refl
    ; tagName = managerCClayReframeTagName
    ; tagNameIsCanonical = refl
    ; clayYangMillsPromoted = false
    ; clayYangMillsPromotedIsFalse = refl
    ; clayNavierStokesPromoted = false
    ; clayNavierStokesPromotedIsFalse = refl
    ; ckmFinalPromoted = false
    ; ckmFinalPromotedIsFalse = refl
    ; exactStandardModelPromoted = false
    ; exactStandardModelPromotedIsFalse = refl
    ; terminalClaimPromoted = false
    ; terminalClaimPromotedIsFalse = refl
    ; promotionFlags = []
    ; promotionFlagsAreEmpty = refl
    }

managerCClayReframeKeepsTerminalFalse :
  terminalClaimPromoted canonicalManagerCClayReframeReceipt ≡ false
managerCClayReframeKeepsTerminalFalse =
  refl
