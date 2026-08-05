module DASHI.Physics.Closure.NSTriadKNLuoFiniteHighHighLowCriticalAssemblyExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- PURPOSE
-- Close the finite summation step behind the high--high to low estimate.
-- Each cell represents one comparable high-input pair p,p' feeding output q
-- and supplies the continuum producer bound
--
--   interaction_cell <= coefficient_cell * A_q * E_q.
--
-- The theorem proves exactly
--
--   sum interaction_cell
--     <= (sum coefficient_cell) * A_q * E_q.
--
-- The dyadic coefficient arithmetic, including the squared
-- 2^(-3 gap/2) calibration and the 8/7 l2 prefix bound, is supplied by the
-- imported round-eleven module.  No Fourier-product estimate is hidden here:
-- every cellwise analytic estimate remains an explicit input field.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteHighHighLowBernsteinGainExact

record HighHighLowCell : Set where
  constructor high-high-low-cell
  field
    interactionMagnitude gapCoefficient : ℚ

open HighHighLowCell public

sumInteraction : List HighHighLowCell → ℚ
sumInteraction [] = 0ℚ
sumInteraction (cell ∷ cells) =
  interactionMagnitude cell + sumInteraction cells

sumCoefficient : List HighHighLowCell → ℚ
sumCoefficient [] = 0ℚ
sumCoefficient (cell ∷ cells) =
  gapCoefficient cell + sumCoefficient cells

record FiniteHighHighLowBudget : Set₁ where
  constructor finite-high-high-low-budget
  field
    cells : List HighHighLowCell
    criticalRoot outputEnergy : ℚ
    cellBound :
      (cell : HighHighLowCell) →
      interactionMagnitude cell
      ≤ gapCoefficient cell * criticalRoot * outputEnergy

open FiniteHighHighLowBudget public

sumScaledCoefficients :
  (cells : List HighHighLowCell) →
  (criticalRoot outputEnergy : ℚ) →
  ℚ
sumScaledCoefficients [] criticalRoot outputEnergy = 0ℚ
sumScaledCoefficients (cell ∷ cells) criticalRoot outputEnergy =
  gapCoefficient cell * criticalRoot * outputEnergy
  + sumScaledCoefficients cells criticalRoot outputEnergy

sumCellBoundsFrom :
  (budget : FiniteHighHighLowBudget) →
  (remaining : List HighHighLowCell) →
  sumInteraction remaining
  ≤ sumScaledCoefficients
      remaining
      (criticalRoot budget)
      (outputEnergy budget)
sumCellBoundsFrom budget [] = ℚₚ.≤-refl
sumCellBoundsFrom budget (cell ∷ remaining) =
  ℚₚ.+-mono-≤
    (cellBound budget cell)
    (sumCellBoundsFrom budget remaining)

sumCellBounds :
  (budget : FiniteHighHighLowBudget) →
  sumInteraction (cells budget)
  ≤ sumScaledCoefficients
      (cells budget)
      (criticalRoot budget)
      (outputEnergy budget)
sumCellBounds budget = sumCellBoundsFrom budget (cells budget)

sumScaledCoefficientsFactor :
  (cells : List HighHighLowCell) →
  (criticalRoot outputEnergy : ℚ) →
  sumScaledCoefficients cells criticalRoot outputEnergy
  ≡ sumCoefficient cells * criticalRoot * outputEnergy
sumScaledCoefficientsFactor [] criticalRoot outputEnergy =
  solve (criticalRoot ∷ outputEnergy ∷ [])
sumScaledCoefficientsFactor (cell ∷ cells) criticalRoot outputEnergy
  rewrite sumScaledCoefficientsFactor cells criticalRoot outputEnergy =
  solve
    ( gapCoefficient cell
    ∷ sumCoefficient cells
    ∷ criticalRoot
    ∷ outputEnergy
    ∷ [])

finiteHighHighLowCriticalAssembly :
  (budget : FiniteHighHighLowBudget) →
  sumInteraction (cells budget)
  ≤ sumCoefficient (cells budget)
      * criticalRoot budget
      * outputEnergy budget
finiteHighHighLowCriticalAssembly budget =
  subst
    (λ upper → sumInteraction (cells budget) ≤ upper)
    (sumScaledCoefficientsFactor
      (cells budget)
      (criticalRoot budget)
      (outputEnergy budget))
    (sumCellBounds budget)
