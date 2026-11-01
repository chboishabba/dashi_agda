module DASHI.Physics.Closure.NSTriadKNNineOwnerDualSensitivityRound40Exact where

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
-- Round 39 made a Farkas certificate an exact *failure witness* for the
-- nine-owner reserve.  Round 40 also uses the dual before the owner programme
-- is complete: the weighted lower-bound contribution
--
--   pressure_j = lambda_j b_j
--
-- records exactly how much each physical constraint contributes to the dual
-- obstruction `combinedLower`.
--
-- This module proves the finite decomposition and exact head-removal law.  A
-- large dual pressure is therefore a mathematically meaningful sensitivity
-- signal for where improving a physical estimate can buy reserve.  It does not
-- claim that dual pressure alone is a derivative of the optimum; it is an
-- exact decomposition of the current rational certificate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNNineOwnerDualNoGoRound39Exact as Dual

cellPressure : Dual.DualConstraintCell → ℚ
cellPressure cell =
  Dual.multiplier cell * Dual.lowerBound (Dual.constraint cell)

sumCellPressure : List Dual.DualConstraintCell → ℚ
sumCellPressure [] = 0ℚ
sumCellPressure (cell ∷ rest) =
  cellPressure cell + sumCellPressure rest

combinedLowerIsSumCellPressure :
  ∀ cells → Dual.combinedLower cells ≡ sumCellPressure cells
combinedLowerIsSumCellPressure [] = refl
combinedLowerIsSumCellPressure (cell ∷ rest) =
  cong (cellPressure cell +_) (combinedLowerIsSumCellPressure rest)

headRemovalLowerExact :
  ∀ cell rest →
  Dual.combinedLower (cell ∷ rest)
  ≡ cellPressure cell + Dual.combinedLower rest
headRemovalLowerExact cell rest = refl

headRemovalNormalExact :
  ∀ cell rest →
  Dual.combinedNormal (cell ∷ rest)
  ≡ Dual.vectorAdd
      (Dual.vectorScale (Dual.multiplier cell)
        (Dual.normal (Dual.constraint cell)))
      (Dual.combinedNormal rest)
headRemovalNormalExact cell rest = refl

record DominantDualPressure
    (cell : Dual.DualConstraintCell)
    (rest : List Dual.DualConstraintCell) : Set where
  field
    cellPressureNonnegative : 0ℚ ≤ cellPressure cell
    restPressureNonnegative : 0ℚ ≤ sumCellPressure rest
    dominatesRest : sumCellPressure rest ≤ cellPressure cell

open DominantDualPressure public

dominantCellCarriesAtLeastHalfCombinedPressure :
  ∀ {cell rest} →
  DominantDualPressure cell rest →
  sumCellPressure (cell ∷ rest)
  ≤ cellPressure cell + cellPressure cell
dominantCellCarriesAtLeastHalfCombinedPressure witness =
  ℚP.+-mono-≤ ℚP.≤-refl (dominatesRest witness)

record DualPressureImprovement
    (cell : Dual.DualConstraintCell) : Set where
  field
    improvedLowerBound : ℚ
    improvedPressure : ℚ
    improvedPressureMeaning :
      improvedPressure
      ≡ Dual.multiplier cell * improvedLowerBound
    pressureDoesNotIncrease : improvedPressure ≤ cellPressure cell

open DualPressureImprovement public

headImprovementReducesCertificateLower :
  ∀ {cell rest}
    (improvement : DualPressureImprovement cell) →
  improvedPressure improvement + sumCellPressure rest
  ≤ sumCellPressure (cell ∷ rest)
headImprovementReducesCertificateLower improvement =
  ℚP.+-mono-≤
    (pressureDoesNotIncrease improvement)
    ℚP.≤-refl

nineOwnerDualSensitivityClosed : Bool
nineOwnerDualSensitivityClosed = true

physicalPartialDualSensitivityCertificateConstructed : Bool
physicalPartialDualSensitivityCertificateConstructed = false

nineOwnerDualSensitivityClosedIsTrue :
  nineOwnerDualSensitivityClosed ≡ true
nineOwnerDualSensitivityClosedIsTrue = refl
