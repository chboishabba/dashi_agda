module DASHI.Physics.Closure.ClayNSProofRoadmapReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.ClayBlockerUpdateReceipt as Blocker
import DASHI.Physics.Closure.HaarFrameBoundsReceipt as Frame
import DASHI.Physics.Closure.NSFrameBoundImplicationReceipt as FrameImp
import DASHI.Physics.Closure.NSWeakSolutionFinalReceipt as Weak
import DASHI.Physics.Closure.WaveletFrameBoundRevisionReceipt as FrameRev

------------------------------------------------------------------------
-- Navier-Stokes Clay roadmap receipt.
--
-- This receipt records the sharpened NS packet posture.  The weak-solution
-- and BKM/global-regularity branches remain separated, and the repo now
-- treats `A1.1-A3.4`, `A4.1-A4.5`, and downstream `A5-A9` as exact
-- candidate theorem packages pending promotion acceptance in the precise
-- downstream norms.  No Clay-facing promotion occurs here.

data NSRoadmapLemma : Set where
  lerayEnergyInequality :
    NSRoadmapLemma

  localSmoothExistenceAuthority :
    NSRoadmapLemma

  enstrophyVorticityControl :
    NSRoadmapLemma

  bkmContinuationCriterion :
    NSRoadmapLemma

  vorticityLInfinityControl :
    NSRoadmapLemma

  globalSmoothContinuation :
    NSRoadmapLemma

  coefficientwiseCompactness :
    NSRoadmapLemma

  archimedeanL2FrameBridge :
    NSRoadmapLemma

  nonlinearTermPassage :
    NSRoadmapLemma

  lerayWeakSolutionLimit :
    NSRoadmapLemma

canonicalNSRoadmapLemmas : List NSRoadmapLemma
canonicalNSRoadmapLemmas =
  lerayEnergyInequality
  ∷ localSmoothExistenceAuthority
  ∷ enstrophyVorticityControl
  ∷ bkmContinuationCriterion
  ∷ vorticityLInfinityControl
  ∷ globalSmoothContinuation
  ∷ coefficientwiseCompactness
  ∷ archimedeanL2FrameBridge
  ∷ nonlinearTermPassage
  ∷ lerayWeakSolutionLimit
  ∷ []

nsRoadmapDocPath : String
nsRoadmapDocPath =
  "Docs/ClayNSProofRoadmap.md"

nsRoadmapStatement : String
nsRoadmapStatement =
  "Clay NS roadmap separates the conditional Leray weak-solution branch from the BKM/global-regularity branch; the repo records candidate-complete A1/A3, A4, and downstream A5-A9 packets pending promotion acceptance, with all Clay-facing flags still false."

record ClayNSProofRoadmapReceipt : Setω where
  field
    blockerUpdateReceipt :
      Blocker.ClayBlockerUpdateReceipt

    blockerUpdateKeepsNSClayFalse :
      Blocker.clayNavierStokesPromoted blockerUpdateReceipt ≡ false

    blockerUpdateKeepsTerminalFalse :
      Blocker.terminalClayClaimPromoted blockerUpdateReceipt ≡ false

    frameReceipt :
      Frame.HaarFrameBoundsReceipt

    frameBoundStillFalse :
      Frame.frameConditionSatisfied frameReceipt ≡ false

    frameRevisionReceipt :
      FrameRev.WaveletFrameBoundRevisionReceipt

    frameRevisionKeepsClayFalse :
      FrameRev.clayPromoted frameRevisionReceipt ≡ false

    weakSolutionReceipt :
      Weak.NSWeakSolutionFinalReceipt

    weakSolutionUnconditionalFalse :
      Weak.nsWeakSolutionUnconditional weakSolutionReceipt ≡ false

    weakSolutionClayFalse :
      Weak.clayNavierStokesPromoted weakSolutionReceipt ≡ false

    frameImplicationReceipt :
      FrameImp.NSFrameBoundImplicationReceipt

    frameImplicationClayFalse :
      FrameImp.clayNavierStokesPromoted frameImplicationReceipt ≡ false

    roadmapDoc :
      String

    roadmapDocIsCanonical :
      roadmapDoc ≡ nsRoadmapDocPath

    lemmaCount :
      Nat

    lemmaCountIsTen :
      lemmaCount ≡ 10

    lemmas :
      List NSRoadmapLemma

    lemmasAreCanonical :
      lemmas ≡ canonicalNSRoadmapLemmas

    weakSolutionBranchSeparated :
      Bool

    weakSolutionBranchSeparatedIsTrue :
      weakSolutionBranchSeparated ≡ true

    bkmBarrierRecorded :
      Bool

    bkmBarrierRecordedIsTrue :
      bkmBarrierRecorded ≡ true

    archimedeanFrameBoundsProved :
      Bool

    archimedeanFrameBoundsProvedIsFalse :
      archimedeanFrameBoundsProved ≡ false

    bkmEnstrophyClosed :
      Bool

    bkmEnstrophyClosedIsFalse :
      bkmEnstrophyClosed ≡ false

    smoothGlobalRegularityProved :
      Bool

    smoothGlobalRegularityProvedIsFalse :
      smoothGlobalRegularityProved ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ nsRoadmapStatement

    receiptBoundary :
      List String

open ClayNSProofRoadmapReceipt public

canonicalClayNSProofRoadmapReceipt :
  ClayNSProofRoadmapReceipt
canonicalClayNSProofRoadmapReceipt =
  record
    { blockerUpdateReceipt =
        Blocker.canonicalClayBlockerUpdateReceipt
    ; blockerUpdateKeepsNSClayFalse =
        refl
    ; blockerUpdateKeepsTerminalFalse =
        refl
    ; frameReceipt =
        Frame.canonicalHaarFrameBoundsReceipt
    ; frameBoundStillFalse =
        refl
    ; frameRevisionReceipt =
        FrameRev.canonicalWaveletFrameBoundRevisionReceipt
    ; frameRevisionKeepsClayFalse =
        refl
    ; weakSolutionReceipt =
        Weak.canonicalNSWeakSolutionFinalReceipt
    ; weakSolutionUnconditionalFalse =
        refl
    ; weakSolutionClayFalse =
        refl
    ; frameImplicationReceipt =
        FrameImp.canonicalNSFrameBoundImplicationReceipt
    ; frameImplicationClayFalse =
        refl
    ; roadmapDoc =
        nsRoadmapDocPath
    ; roadmapDocIsCanonical =
        refl
    ; lemmaCount =
        10
    ; lemmaCountIsTen =
        refl
    ; lemmas =
        canonicalNSRoadmapLemmas
    ; lemmasAreCanonical =
        refl
    ; weakSolutionBranchSeparated =
        true
    ; weakSolutionBranchSeparatedIsTrue =
        refl
    ; bkmBarrierRecorded =
        true
    ; bkmBarrierRecordedIsTrue =
        refl
    ; archimedeanFrameBoundsProved =
        false
    ; archimedeanFrameBoundsProvedIsFalse =
        refl
    ; bkmEnstrophyClosed =
        false
    ; bkmEnstrophyClosedIsFalse =
        refl
    ; smoothGlobalRegularityProved =
        false
    ; smoothGlobalRegularityProvedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; statement =
        nsRoadmapStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        "The roadmap is a dependency graph, not a proof"
        ∷ "The weak-solution branch stays conditional on frame and nonlinear-passage lemmas"
        ∷ "A1.1-A3.4 is recorded as an exact candidate package pending promotion acceptance"
        ∷ "A4.1-A4.5 is recorded as an exact candidate package pending promotion acceptance"
        ∷ "A5-A9 is recorded as an exact downstream consumer package pending upstream acceptance"
        ∷ "The BKM/enstrophy branch remains uninhabited and Clay/terminal promotion remain false"
        ∷ []
    }

clayNSRoadmapKeepsClayFalse :
  clayNavierStokesPromoted canonicalClayNSProofRoadmapReceipt ≡ false
clayNSRoadmapKeepsClayFalse =
  refl

clayNSRoadmapKeepsTerminalFalse :
  terminalClaimPromoted canonicalClayNSProofRoadmapReceipt ≡ false
clayNSRoadmapKeepsTerminalFalse =
  refl
