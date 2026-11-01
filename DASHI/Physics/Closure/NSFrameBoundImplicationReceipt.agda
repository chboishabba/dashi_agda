module DASHI.Physics.Closure.NSFrameBoundImplicationReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.MutualOrthogonalityGeneralProofReceipt as Ortho
import DASHI.Physics.Closure.NSWeakSolutionFinalReceipt as NS

------------------------------------------------------------------------
-- Conditional frame-bound implication for the NS passage.

conditionalFrameStatement : String
conditionalFrameStatement =
  "If the dyadic, triadic, and pentadic Haar systems are mutually orthogonal frames, their union is a tight frame with bound 3, so coefficient l2 convergence is equivalent to L2(R3) convergence up to that frame bound."

record NSFrameBoundImplicationReceipt : Setω where
  field
    orthogonalityReceipt :
      Ortho.MutualOrthogonalityGeneralProofReceipt

    orthogonalityStillOpen :
      Ortho.allScaleMutualOrthogonalityProved orthogonalityReceipt
      ≡
      false

    weakSolutionReceipt :
      NS.NSWeakSolutionFinalReceipt

    weakSolutionStillConditional :
      NS.nsWeakSolutionUnconditional weakSolutionReceipt ≡ false

    nsFrameBoundConditional :
      Bool

    nsFrameBoundConditionalIsTrue :
      nsFrameBoundConditional ≡ true

    conditionalFrameBoundValue :
      String

    conditionalFrameBoundValueIsThree :
      conditionalFrameBoundValue ≡ "3"

    nsL2ConvergenceFromFrameCoefficients :
      Bool

    nsL2ConvergenceFromFrameCoefficientsIsConditional :
      nsL2ConvergenceFromFrameCoefficients ≡ true

    unconditionalFrameBoundProved :
      Bool

    unconditionalFrameBoundProvedIsFalse :
      unconditionalFrameBoundProved ≡ false

    unconditionalNSWeakSolution :
      Bool

    unconditionalNSWeakSolutionIsFalse :
      unconditionalNSWeakSolution ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ conditionalFrameStatement

    receiptBoundary :
      List String

open NSFrameBoundImplicationReceipt public

canonicalNSFrameBoundImplicationReceipt :
  NSFrameBoundImplicationReceipt
canonicalNSFrameBoundImplicationReceipt =
  record
    { orthogonalityReceipt =
        Ortho.canonicalMutualOrthogonalityGeneralProofReceipt
    ; orthogonalityStillOpen =
        refl
    ; weakSolutionReceipt =
        NS.canonicalNSWeakSolutionFinalReceipt
    ; weakSolutionStillConditional =
        refl
    ; nsFrameBoundConditional =
        true
    ; nsFrameBoundConditionalIsTrue =
        refl
    ; conditionalFrameBoundValue =
        "3"
    ; conditionalFrameBoundValueIsThree =
        refl
    ; nsL2ConvergenceFromFrameCoefficients =
        true
    ; nsL2ConvergenceFromFrameCoefficientsIsConditional =
        refl
    ; unconditionalFrameBoundProved =
        false
    ; unconditionalFrameBoundProvedIsFalse =
        refl
    ; unconditionalNSWeakSolution =
        false
    ; unconditionalNSWeakSolutionIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; statement =
        conditionalFrameStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        "The bound-3 statement is conditional on all-scale mutual orthogonality or equivalent frame bounds"
        ∷ "The receipt records the implication, not the missing harmonic-analysis proof"
        ∷ "No unconditional Navier-Stokes weak or smooth continuum theorem follows"
        ∷ []
    }

nsFrameBoundImplicationKeepsClayFalse :
  clayNavierStokesPromoted canonicalNSFrameBoundImplicationReceipt
  ≡
  false
nsFrameBoundImplicationKeepsClayFalse =
  refl

