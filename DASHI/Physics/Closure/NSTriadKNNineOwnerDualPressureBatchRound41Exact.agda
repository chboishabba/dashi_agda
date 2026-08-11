module DASHI.Physics.Closure.NSTriadKNNineOwnerDualPressureBatchRound41Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- Author: Gyula Farkas.
-- Title: "Theorie der einfachen Ungleichungen".
-- Journal fuer die reine und angewandte Mathematik 124 (1902), 1--27.
-- DOI: no DOI assigned to the historical article.
--
-- DASHI CONTRIBUTION
--
-- Round 40 decomposed the nine-owner dual obstruction into exact pressures
--
--   p_j = lambda_j b_j
--
-- and showed that improving one lower bound cannot increase the combined dual
-- lower value.  The proof-search loop in the attached analysis needs the batch
-- version: if several physical estimates are sharpened, how much exact dual
-- obstruction is removed?
--
-- A batch cell stores one Round-40 improvement.  Its saving is
--
--   p_old - p_new >= 0.
--
-- Finite summation proves
--
--   newPressureTotal + savingTotal = oldPressureTotal.
--
-- Thus provisional physical constants can be ranked and improved using an
-- exact rational certificate of how much *current* dual obstruction is being
-- removed.  This remains sensitivity of a fixed certificate, not a derivative
-- of the optimized value.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNNineOwnerDualNoGoRound39Exact as Dual
import DASHI.Physics.Closure.NSTriadKNNineOwnerDualSensitivityRound40Exact as Sensitivity

record DualPressureBatchCell : Set where
  field
    originalCell : Dual.DualConstraintCell
    improvement : Sensitivity.DualPressureImprovement originalCell

open DualPressureBatchCell public

oldPressure newPressure saving : DualPressureBatchCell → ℚ
oldPressure cell = Sensitivity.cellPressure (originalCell cell)
newPressure cell = Sensitivity.improvedPressure (improvement cell)
saving cell = oldPressure cell - newPressure cell

savingNonnegative : ∀ cell → 0ℚ ≤ saving cell
savingNonnegative cell =
  let
    bound = Sensitivity.pressureDoesNotIncrease (improvement cell)
    shifted :
      newPressure cell - newPressure cell
      ≤ oldPressure cell - newPressure cell
    shifted = ℚP.+-monoʳ-≤ (- newPressure cell) bound
  in
  subst
    (λ lower → lower ≤ saving cell)
    (solve (newPressure cell ∷ []))
    shifted

newPlusSavingEqualsOld : ∀ cell →
  newPressure cell + saving cell ≡ oldPressure cell
newPlusSavingEqualsOld cell =
  solve (newPressure cell ∷ oldPressure cell ∷ [])

sumOldPressure sumNewPressure sumSaving : List DualPressureBatchCell → ℚ
sumOldPressure [] = 0ℚ
sumOldPressure (cell ∷ rest) = oldPressure cell + sumOldPressure rest

sumNewPressure [] = 0ℚ
sumNewPressure (cell ∷ rest) = newPressure cell + sumNewPressure rest

sumSaving [] = 0ℚ
sumSaving (cell ∷ rest) = saving cell + sumSaving rest

sumSavingNonnegative : ∀ cells → 0ℚ ≤ sumSaving cells
sumSavingNonnegative [] = ℚP.≤-refl
sumSavingNonnegative (cell ∷ rest) =
  L2.addNonnegative (savingNonnegative cell) (sumSavingNonnegative rest)

batchPressureConservation : ∀ cells →
  sumNewPressure cells + sumSaving cells ≡ sumOldPressure cells
batchPressureConservation [] = refl
batchPressureConservation (cell ∷ rest)
  rewrite batchPressureConservation rest
        | newPlusSavingEqualsOld cell =
  solve
    ( oldPressure cell
    ∷ sumOldPressure rest
    ∷ sumNewPressure rest
    ∷ sumSaving rest
    ∷ [])

batchNewPressureCannotExceedOld : ∀ cells →
  sumNewPressure cells ≤ sumOldPressure cells
batchNewPressureCannotExceedOld cells =
  let
    savingNN = sumSavingNonnegative cells
    addSaving :
      sumNewPressure cells + 0ℚ
      ≤ sumNewPressure cells + sumSaving cells
    addSaving = ℚP.+-monoʳ-≤ (sumNewPressure cells) savingNN
  in
  subst
    (λ lower → lower ≤ sumOldPressure cells)
    (solve (sumNewPressure cells ∷ []))
    (subst
      (λ upper → sumNewPressure cells + 0ℚ ≤ upper)
      (batchPressureConservation cells)
      addSaving)

nineOwnerDualPressureBatchClosed : Bool
nineOwnerDualPressureBatchClosed = true

physicalDualPressureBatchFromOwnerConstantsConstructed : Bool
physicalDualPressureBatchFromOwnerConstantsConstructed = false

nineOwnerDualPressureBatchClosedIsTrue :
  nineOwnerDualPressureBatchClosed ≡ true
nineOwnerDualPressureBatchClosedIsTrue = refl
