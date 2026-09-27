{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumMereologySchwingerObjectiveExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Quantum.QuantumMereologyExact as QM
import DASHI.Quantum.QuantumMereologySelectionExact as Selection
import DASHI.Quantum.QuantumMereologySourceAtlasExact as Sources

------------------------------------------------------------------------
-- SOURCE-EXACT SCHWINGER-OBJECTIVE STRUCTURE
--
-- Carroll--Singh source content:
--   S_lin     = 1 - Tr(rho_A^2)
--   S_pointer = 1 - sum_j p_j^2
--   penalties = second time derivatives at t = 0
--   S_Schwinger'' = max(S_lin'', S_pointer'')
--   average over candidate-pointer eigenstate initialisations
--   minimize over fixed-dimension factorizations.
--
-- Lean owns the current concrete real-valued formula reconstruction. Agda owns
-- only the structural selection theorem plus explicit formula-authority sockets.
------------------------------------------------------------------------

record SchwingerSearchData
    (W : QM.BareQuantumWorld) : Set₁ where
  field
    Candidate PointerInit Score : Set

    realizes :
      Candidate → QM.TensorProductStructure W

    Admissible :
      Candidate → Set

    linearEntropyAcceleration :
      Candidate → PointerInit → Score

    pointerEntropyAcceleration :
      Candidate → PointerInit → Score

    maxScore :
      Score → Score → Score

    average :
      (PointerInit → Score) → Score

    ScoreNoWorse :
      Score → Score → Set

open SchwingerSearchData public

schwingerScore :
  ∀ {W} →
  (D : SchwingerSearchData W) →
  Candidate D →
  Score D
schwingerScore D candidate =
  average D
    (λ pointerInit →
      maxScore D
        (linearEntropyAcceleration D candidate pointerInit)
        (pointerEntropyAcceleration D candidate pointerInit))

selectionProblem :
  ∀ {W} →
  (D : SchwingerSearchData W) →
  Selection.PreferredTPSSelectionProblem W
selectionProblem D = record
  { Selection.PreferredTPSSelectionProblem.Candidate =
      Candidate D
  ; Selection.PreferredTPSSelectionProblem.realizes =
      realizes D
  ; Selection.PreferredTPSSelectionProblem.Admissible =
      Admissible D
  ; Selection.PreferredTPSSelectionProblem.EntanglementGrowthScore =
      PointerInit D → Score D
  ; Selection.PreferredTPSSelectionProblem.InternalSpreadingScore =
      PointerInit D → Score D
  ; Selection.PreferredTPSSelectionProblem.entanglementGrowth =
      linearEntropyAcceleration D
  ; Selection.PreferredTPSSelectionProblem.internalSpreading =
      pointerEntropyAcceleration D
  ; Selection.PreferredTPSSelectionProblem.NoWorse =
      λ left right →
        ScoreNoWorse D
          (schwingerScore D left)
          (schwingerScore D right)
  }

selectedMinimizesSchwingerScore :
  ∀ {W}
    (D : SchwingerSearchData W) →
  (receipt :
    Selection.PreferredTPSSelectionReceipt
      (selectionProblem D)) →
  (other : Candidate D) →
  Admissible D other →
  ScoreNoWorse D
    (schwingerScore D
      (Selection.selected receipt))
    (schwingerScore D other)
selectedMinimizesSchwingerScore D receipt other otherAdmissible =
  let optimal = Selection.selectedOptimal receipt
  in
  Agda.Builtin.Sigma.snd optimal other otherAdmissible

------------------------------------------------------------------------
-- FORMULA / PRODUCER AUTHORITY
------------------------------------------------------------------------

record SchwingerFormulaAuthority : Set₁ where
  field
    LinearEntropyFormulaAuthority : Set
    linearEntropyFormulaAuthority :
      LinearEntropyFormulaAuthority

    PointerEntropyFormulaAuthority : Set
    pointerEntropyFormulaAuthority :
      PointerEntropyFormulaAuthority

    ReducedDensityMatrixAuthority : Set
    reducedDensityMatrixAuthority :
      ReducedDensityMatrixAuthority

    SecondTimeDerivativeAuthority : Set
    secondTimeDerivativeAuthority :
      SecondTimeDerivativeAuthority

    CandidatePointerObservableAuthority : Set
    candidatePointerObservableAuthority :
      CandidatePointerObservableAuthority

open SchwingerFormulaAuthority public

record SchwingerObjectivePromotionBoundary : Set where
  field
    formulaNamesCreateReducedDensityMatrix : Bool
    formulaNamesCreateReducedDensityMatrixIsFalse :
      formulaNamesCreateReducedDensityMatrix ≡ false

    formulaNamesCreatePartialTrace : Bool
    formulaNamesCreatePartialTraceIsFalse :
      formulaNamesCreatePartialTrace ≡ false

    sourceAlgorithmCreatesLocalMinimizerExistence : Bool
    sourceAlgorithmCreatesLocalMinimizerExistenceIsFalse :
      sourceAlgorithmCreatesLocalMinimizerExistence ≡ false

    sourceAlgorithmCreatesLocalMinimizerUniqueness : Bool
    sourceAlgorithmCreatesLocalMinimizerUniquenessIsFalse :
      sourceAlgorithmCreatesLocalMinimizerUniqueness ≡ false

canonicalSchwingerObjectivePromotionBoundary :
  SchwingerObjectivePromotionBoundary
canonicalSchwingerObjectivePromotionBoundary = record
  { formulaNamesCreateReducedDensityMatrix = false
  ; formulaNamesCreateReducedDensityMatrixIsFalse = refl
  ; formulaNamesCreatePartialTrace = false
  ; formulaNamesCreatePartialTraceIsFalse = refl
  ; sourceAlgorithmCreatesLocalMinimizerExistence = false
  ; sourceAlgorithmCreatesLocalMinimizerExistenceIsFalse = refl
  ; sourceAlgorithmCreatesLocalMinimizerUniqueness = false
  ; sourceAlgorithmCreatesLocalMinimizerUniquenessIsFalse = refl
  }

carrollSinghSchwingerFormulaClaim : Sources.AttributionReceipt
carrollSinghSchwingerFormulaClaim =
  Sources.attribution-receipt
    Sources.externalSourceClaim
    "Sean M. Carroll; Ashmeet Singh, Phys. Rev. A 103, 022213 (2021)"
    "Defines linear entropy 1-Tr(rho_A^2), pointer entropy 1-sum p_j^2, their second derivatives at t=0, pointwise max as Schwinger entropy, averaging over candidate-pointer eigenstate initialisations, and minimization across fixed-dimension factorizations."

leanSchwingerFormulaSourceWrittenReceipt : Sources.AttributionReceipt
leanSchwingerFormulaSourceWrittenReceipt =
  Sources.attribution-receipt
    Sources.importedFormalTheoremSource
    "DASHI Lean: RequestProject.QuantumMereologySchwingerObjective"
    "Source-written concrete real-valued reconstruction of the Carroll--Singh entropy formula layer. It is not promoted to kernel-certified authority until exact-head Lean build evidence exists."

dashiSchwingerSelectionReconstructionReceipt : Sources.AttributionReceipt
dashiSchwingerSelectionReconstructionReceipt =
  Sources.attribution-receipt
    Sources.localFormalReconstruction
    "DASHI Agda"
    "Reconstructs the pointwise-max/average/minimization selection grammar while leaving reduced states, partial trace, entropy formula realization, derivatives, CPO construction, existence and uniqueness as explicit authorities."
