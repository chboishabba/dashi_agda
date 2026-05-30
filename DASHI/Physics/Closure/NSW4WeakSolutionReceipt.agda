module DASHI.Physics.Closure.NSW4WeakSolutionReceipt where

open import Agda.Primitive using (Set; Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.NSFrameBoundImplicationReceipt as Frame
import DASHI.Physics.Closure.NSWeakSolutionFinalReceipt as Weak

data NSW4WeakSolutionStatus : Set where
  lerayWeakSolutionBranchRecordedRegularityOpen :
    NSW4WeakSolutionStatus

data NSW4WeakSolutionItem : Set where
  coefficientCompactnessBranch :
    NSW4WeakSolutionItem
  conditionalFrameBridgeBranch :
    NSW4WeakSolutionItem
  lerayWeakSolutionBranch :
    NSW4WeakSolutionItem
  clayRegularityGapBoundary :
    NSW4WeakSolutionItem

canonicalNSW4WeakSolutionItems :
  List NSW4WeakSolutionItem
canonicalNSW4WeakSolutionItems =
  coefficientCompactnessBranch
  ∷ conditionalFrameBridgeBranch
  ∷ lerayWeakSolutionBranch
  ∷ clayRegularityGapBoundary
  ∷ []

nsW4WeakSolutionStatement : String
nsW4WeakSolutionStatement =
  "W4 records the Leray weak-solution branch as available under the existing frame/nonlinear-passage receipts; it does not close global smooth regularity, BKM vorticity control, or Clay Navier-Stokes."

record NSW4WeakSolutionReceipt : Setω where
  field
    status :
      NSW4WeakSolutionStatus

    weakSolutionReceipt :
      Weak.NSWeakSolutionFinalReceipt

    weakSolutionConditionalBranchTrue :
      Weak.nsLerayWeakSolutionConditional weakSolutionReceipt ≡ true

    weakSolutionUnconditionalFalse :
      Weak.nsWeakSolutionUnconditional weakSolutionReceipt ≡ false

    weakSolutionClayFalse :
      Weak.clayNavierStokesPromoted weakSolutionReceipt ≡ false

    frameImplicationReceipt :
      Frame.NSFrameBoundImplicationReceipt

    frameBridgeConditionalTrue :
      Frame.nsL2ConvergenceFromFrameCoefficients
        frameImplicationReceipt
      ≡
      true

    frameBridgeUnconditionalFalse :
      Frame.unconditionalFrameBoundProved frameImplicationReceipt ≡ false

    trancheItems :
      List NSW4WeakSolutionItem

    trancheItemsAreCanonical :
      trancheItems ≡ canonicalNSW4WeakSolutionItems

    lerayWeakSolutionBranchAvailable :
      Bool

    lerayWeakSolutionBranchAvailableIsTrue :
      lerayWeakSolutionBranchAvailable ≡ true

    globalSmoothRegularityProved :
      Bool

    globalSmoothRegularityProvedIsFalse :
      globalSmoothRegularityProved ≡ false

    bkmVorticityControlClosed :
      Bool

    bkmVorticityControlClosedIsFalse :
      bkmVorticityControlClosed ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ nsW4WeakSolutionStatement

    receiptBoundary :
      List String

open NSW4WeakSolutionReceipt public

canonicalNSW4WeakSolutionReceipt :
  NSW4WeakSolutionReceipt
canonicalNSW4WeakSolutionReceipt =
  record
    { status =
        lerayWeakSolutionBranchRecordedRegularityOpen
    ; weakSolutionReceipt =
        Weak.canonicalNSWeakSolutionFinalReceipt
    ; weakSolutionConditionalBranchTrue =
        refl
    ; weakSolutionUnconditionalFalse =
        refl
    ; weakSolutionClayFalse =
        refl
    ; frameImplicationReceipt =
        Frame.canonicalNSFrameBoundImplicationReceipt
    ; frameBridgeConditionalTrue =
        refl
    ; frameBridgeUnconditionalFalse =
        refl
    ; trancheItems =
        canonicalNSW4WeakSolutionItems
    ; trancheItemsAreCanonical =
        refl
    ; lerayWeakSolutionBranchAvailable =
        true
    ; lerayWeakSolutionBranchAvailableIsTrue =
        refl
    ; globalSmoothRegularityProved =
        false
    ; globalSmoothRegularityProvedIsFalse =
        refl
    ; bkmVorticityControlClosed =
        false
    ; bkmVorticityControlClosedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; statement =
        nsW4WeakSolutionStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        "The Leray weak-solution branch is the only true branch recorded here"
        ∷ "The frame bridge remains conditional and is not an unconditional harmonic-analysis closure"
        ∷ "BKM vorticity control, global smoothness, and Clay promotion remain false"
        ∷ []
    }

nsW4WeakSolutionKeepsClayFalse :
  clayNavierStokesPromoted canonicalNSW4WeakSolutionReceipt ≡ false
nsW4WeakSolutionKeepsClayFalse =
  refl
