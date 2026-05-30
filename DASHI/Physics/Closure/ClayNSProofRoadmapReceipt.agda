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
-- This receipt records that the human-readable proof roadmap exists and
-- separates the weak-solution branch from the BKM/global-regularity branch.

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
  "Clay NS roadmap separates the conditional Leray weak-solution branch from the BKM/global-regularity branch; current carrier progress is conditional and frame-bound blocked."

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
        ∷ "The weak-solution branch is conditional on frame and nonlinear-passage lemmas"
        ∷ "The BKM/enstrophy branch is separate and remains uninhabited"
        ∷ "Clay Navier-Stokes and terminal promotion remain false"
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
