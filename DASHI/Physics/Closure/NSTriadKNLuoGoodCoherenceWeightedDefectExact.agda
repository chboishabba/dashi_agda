module DASHI.Physics.Closure.NSTriadKNLuoGoodCoherenceWeightedDefectExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier--Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- PURPOSE
-- Prove the complementary finite good-coherence estimate. On every good cell
-- the directional defect theta satisfies
--
--   theta <= delta.
--
-- For nonnegative interaction weights this gives
--
--   weightedDefectMass <= delta * goodWeightMass.
--
-- This is the exact finite source of the geometric delta_q gain. Identifying
-- the physical vortex-stretching cell weight and proving the resulting good
-- interaction estimate remain analytic carrier obligations.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold

record GoodCoherenceCell (parameter : Threshold.PositiveThreshold) : Set where
  constructor good-coherence-cell
  field
    weight defect : ℚ
    weightNonnegative : 0ℚ ≤ weight
    defectNonnegative : 0ℚ ≤ defect
    goodThreshold : defect ≤ Threshold.threshold parameter

open GoodCoherenceCell public

goodWeightMass :
  (parameter : Threshold.PositiveThreshold) →
  List (GoodCoherenceCell parameter) →
  ℚ
goodWeightMass parameter [] = 0ℚ
goodWeightMass parameter (cell ∷ cells) =
  weight cell + goodWeightMass parameter cells

goodWeightedDefectMass :
  (parameter : Threshold.PositiveThreshold) →
  List (GoodCoherenceCell parameter) →
  ℚ
goodWeightedDefectMass parameter [] = 0ℚ
goodWeightedDefectMass parameter (cell ∷ cells) =
  weight cell * defect cell + goodWeightedDefectMass parameter cells

goodWeightMassNonnegative :
  (parameter : Threshold.PositiveThreshold) →
  (cells : List (GoodCoherenceCell parameter)) →
  0ℚ ≤ goodWeightMass parameter cells
goodWeightMassNonnegative parameter [] = ℚₚ.≤-refl
goodWeightMassNonnegative parameter (cell ∷ cells) =
  L2.addNonnegative
    (weightNonnegative cell)
    (goodWeightMassNonnegative parameter cells)

goodWeightedDefectBelowThresholdMass :
  (parameter : Threshold.PositiveThreshold) →
  (cells : List (GoodCoherenceCell parameter)) →
  goodWeightedDefectMass parameter cells
  ≤ Threshold.threshold parameter * goodWeightMass parameter cells
goodWeightedDefectBelowThresholdMass parameter [] = ℚₚ.≤-refl
goodWeightedDefectBelowThresholdMass parameter (cell ∷ cells) =
  let
    local :
      weight cell * defect cell
      ≤ weight cell * Threshold.threshold parameter
    local =
      L2.nonnegativeProductMonotone
        (weightNonnegative cell)
        (defectNonnegative cell)
        (weightNonnegative cell)
        (Threshold.thresholdNonnegative parameter)
        ℚₚ.≤-refl
        (goodThreshold cell)

    tail = goodWeightedDefectBelowThresholdMass parameter cells
    summed = ℚₚ.+-mono-≤ local tail

    rightDistributed :
      weight cell * Threshold.threshold parameter
        + Threshold.threshold parameter * goodWeightMass parameter cells
      ≡ Threshold.threshold parameter
        * (weight cell + goodWeightMass parameter cells)
    rightDistributed =
      solve
        ( Threshold.threshold parameter
        ∷ weight cell
        ∷ goodWeightMass parameter cells
        ∷ [])
  in
  subst
    (λ upper →
      weight cell * defect cell
        + goodWeightedDefectMass parameter cells
      ≤ upper)
    rightDistributed
    summed
