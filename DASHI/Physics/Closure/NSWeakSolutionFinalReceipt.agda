module DASHI.Physics.Closure.NSWeakSolutionFinalReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.NSCarrierContinuumLimitReceipt as Limit
import DASHI.Physics.Closure.WaveletOrthogonalityProofReceipt as Wavelet

------------------------------------------------------------------------
-- Final weak-solution passage ledger, conditional on the frame bridge.

data NSWeakSolutionIngredient : Set where
  coefficientwiseAubinLions :
    NSWeakSolutionIngredient

  rieszOrFrameBridge :
    NSWeakSolutionIngredient

  strongL2Convergence :
    NSWeakSolutionIngredient

  nonlinearDistributionalPassage :
    NSWeakSolutionIngredient

canonicalNSWeakSolutionIngredients :
  List NSWeakSolutionIngredient
canonicalNSWeakSolutionIngredients =
  coefficientwiseAubinLions
  ∷ rieszOrFrameBridge
  ∷ strongL2Convergence
  ∷ nonlinearDistributionalPassage
  ∷ []

data NSWeakSolutionBlocker : Set where
  missingRieszFrameBounds :
    NSWeakSolutionBlocker

  missingCoefficientToL2Continuity :
    NSWeakSolutionBlocker

  missingUnconditionalNonlinearPassage :
    NSWeakSolutionBlocker

  missingBKMSmoothPassage :
    NSWeakSolutionBlocker

canonicalNSWeakSolutionBlockers :
  List NSWeakSolutionBlocker
canonicalNSWeakSolutionBlockers =
  missingRieszFrameBounds
  ∷ missingCoefficientToL2Continuity
  ∷ missingUnconditionalNonlinearPassage
  ∷ missingBKMSmoothPassage
  ∷ []

weakSolutionStatement : String
weakSolutionStatement =
  "If the 2/3/5 wavelet system supplies frame bounds and coefficient-to-L2 continuity, then coefficientwise Aubin-Lions gives a Leray weak-solution limit; this receipt records the conditional route only."

record NSWeakSolutionFinalReceipt : Setω where
  field
    continuumLimitReceipt :
      Limit.NSCarrierContinuumLimitReceipt

    nonlinearPassageOnlyConditional :
      Limit.nsWeakSolutionLimitInhabitedUnconditionally continuumLimitReceipt
      ≡
      false

    waveletOrthogonalityReceipt :
      Wavelet.WaveletOrthogonalityProofReceipt

    rieszBasisStillOpen :
      Wavelet.rieszBasisProved waveletOrthogonalityReceipt ≡ false

    ingredients :
      List NSWeakSolutionIngredient

    ingredientsAreCanonical :
      ingredients ≡ canonicalNSWeakSolutionIngredients

    nsWeakSolutionFromRieszBasis :
      Bool

    nsWeakSolutionFromRieszBasisIsConditional :
      nsWeakSolutionFromRieszBasis ≡ true

    nsLerayWeakSolutionConditional :
      Bool

    nsLerayWeakSolutionConditionalIsTrue :
      nsLerayWeakSolutionConditional ≡ true

    nsWeakSolutionUnconditional :
      Bool

    nsWeakSolutionUnconditionalIsFalse :
      nsWeakSolutionUnconditional ≡ false

    nsSmoothContinuumLimit :
      Bool

    nsSmoothContinuumLimitIsFalse :
      nsSmoothContinuumLimit ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    blockers :
      List NSWeakSolutionBlocker

    blockersAreCanonical :
      blockers ≡ canonicalNSWeakSolutionBlockers

    statement :
      String

    statementIsCanonical :
      statement ≡ weakSolutionStatement

    receiptBoundary :
      List String

open NSWeakSolutionFinalReceipt public

canonicalNSWeakSolutionFinalReceipt :
  NSWeakSolutionFinalReceipt
canonicalNSWeakSolutionFinalReceipt =
  record
    { continuumLimitReceipt =
        Limit.canonicalNSCarrierContinuumLimitReceipt
    ; nonlinearPassageOnlyConditional =
        refl
    ; waveletOrthogonalityReceipt =
        Wavelet.canonicalWaveletOrthogonalityProofReceipt
    ; rieszBasisStillOpen =
        refl
    ; ingredients =
        canonicalNSWeakSolutionIngredients
    ; ingredientsAreCanonical =
        refl
    ; nsWeakSolutionFromRieszBasis =
        true
    ; nsWeakSolutionFromRieszBasisIsConditional =
        refl
    ; nsLerayWeakSolutionConditional =
        true
    ; nsLerayWeakSolutionConditionalIsTrue =
        refl
    ; nsWeakSolutionUnconditional =
        false
    ; nsWeakSolutionUnconditionalIsFalse =
        refl
    ; nsSmoothContinuumLimit =
        false
    ; nsSmoothContinuumLimitIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; blockers =
        canonicalNSWeakSolutionBlockers
    ; blockersAreCanonical =
        refl
    ; statement =
        weakSolutionStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        "This is the conditional final weak-solution route, not an unconditional continuum theorem"
        ∷ "Literal multibase orthogonality failed; frame bounds remain the required bridge"
        ∷ "Smoothness, BKM continuation, and Clay Navier-Stokes promotion remain false"
        ∷ []
    }

nsWeakSolutionFinalKeepsClayFalse :
  clayNavierStokesPromoted canonicalNSWeakSolutionFinalReceipt ≡ false
nsWeakSolutionFinalKeepsClayFalse =
  refl

