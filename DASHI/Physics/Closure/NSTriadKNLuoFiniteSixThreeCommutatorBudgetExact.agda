module DASHI.Physics.Closure.NSTriadKNLuoFiniteSixThreeCommutatorBudgetExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Peter Constantin; Weinan E; Edriss S. Titi.
-- Title: "Onsager's Conjecture on the Energy Conservation for Solutions of
-- Euler's Equation".
-- DOI: 10.1007/BF02099744.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Piero D'Ancona.
-- Title: "A Short Proof of Commutator Estimates".
-- DOI: 10.1007/s00041-018-9612-8.
-- Correction DOI: 10.1007/s00041-019-09724-7.
--
-- PURPOSE
-- Assemble the two centered Taylor branches after the exact (L6,L3) exponent
-- calculation.  At gap d=gap+2 the first branch has squared coefficient
-- 2^(-3d), the second 2^(-d).  The former is pointwise below the latter, so a
-- complete cell is bounded by twice the weak shell envelope.  Finite summation
-- preserves this bound exactly.
--
-- The analytic kernel/Hölder/Bernstein step supplies the two branch bounds;
-- the shell arithmetic and complete finite assembly are proved here.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNLuoSixThreeCenteredCommutatorScaleExact as Scale

record SixThreeCommutatorCell : Set where
  constructor six-three-commutator-cell
  field
    gap : Nat
    firstBranchSquared secondBranchSquared : ℚ
    lowCriticalMass outputMass : ℚ

    lowCriticalMassNonnegative : 0ℚ ≤ lowCriticalMass
    outputMassNonnegative : 0ℚ ≤ outputMass

    firstBranchBound :
      firstBranchSquared
      ≤ Scale.strongBranchSquaredGap gap
        * lowCriticalMass * outputMass

    secondBranchBound :
      secondBranchSquared
      ≤ Scale.weakBranchSquaredGap gap
        * lowCriticalMass * outputMass

open SixThreeCommutatorCell public

cellCommutatorSquared : SixThreeCommutatorCell → ℚ
cellCommutatorSquared cell =
  firstBranchSquared cell + secondBranchSquared cell

weakCellEnvelope : SixThreeCommutatorCell → ℚ
weakCellEnvelope cell =
  Scale.weakBranchSquaredGap (gap cell)
  * lowCriticalMass cell * outputMass cell

strongEnvelopeBelowWeak :
  (cell : SixThreeCommutatorCell) →
  Scale.strongBranchSquaredGap (gap cell)
    * lowCriticalMass cell * outputMass cell
  ≤ weakCellEnvelope cell
strongEnvelopeBelowWeak cell =
  let
    scaleLow :
      Scale.strongBranchSquaredGap (gap cell)
        * lowCriticalMass cell
      ≤ Scale.weakBranchSquaredGap (gap cell)
        * lowCriticalMass cell
    scaleLow =
      let
        instance
          lowMassIsNonnegative =
            nonNegative (lowCriticalMassNonnegative cell)
      in
      ℚₚ.*-monoʳ-≤-nonNeg
        (lowCriticalMass cell)
        (Scale.strongBranchDominatedByWeak (gap cell))
  in
  let
    instance
      outputIsNonnegative =
        nonNegative (outputMassNonnegative cell)
  in
  ℚₚ.*-monoʳ-≤-nonNeg (outputMass cell) scaleLow

cellSixThreeBudget :
  (cell : SixThreeCommutatorCell) →
  cellCommutatorSquared cell
  ≤ Scale.two * weakCellEnvelope cell
cellSixThreeBudget cell =
  let
    firstToWeak :
      firstBranchSquared cell ≤ weakCellEnvelope cell
    firstToWeak =
      ℚₚ.≤-trans
        (firstBranchBound cell)
        (strongEnvelopeBelowWeak cell)

    secondToWeak :
      secondBranchSquared cell ≤ weakCellEnvelope cell
    secondToWeak = secondBranchBound cell

    summed :
      firstBranchSquared cell + secondBranchSquared cell
      ≤ weakCellEnvelope cell + weakCellEnvelope cell
    summed = ℚₚ.+-mono-≤ firstToWeak secondToWeak

    targetMeaning :
      weakCellEnvelope cell + weakCellEnvelope cell
      ≡ Scale.two * weakCellEnvelope cell
    targetMeaning = solve (weakCellEnvelope cell ∷ [])
  in
  subst
    (λ upper → cellCommutatorSquared cell ≤ upper)
    targetMeaning
    summed

sumCellCommutatorSquared : List SixThreeCommutatorCell → ℚ
sumCellCommutatorSquared [] = 0ℚ
sumCellCommutatorSquared (cell ∷ cells) =
  cellCommutatorSquared cell + sumCellCommutatorSquared cells

sumWeakCellEnvelope : List SixThreeCommutatorCell → ℚ
sumWeakCellEnvelope [] = 0ℚ
sumWeakCellEnvelope (cell ∷ cells) =
  weakCellEnvelope cell + sumWeakCellEnvelope cells

finiteSixThreeCommutatorBudget :
  (cells : List SixThreeCommutatorCell) →
  sumCellCommutatorSquared cells
  ≤ Scale.two * sumWeakCellEnvelope cells
finiteSixThreeCommutatorBudget [] = ℚₚ.≤-refl
finiteSixThreeCommutatorBudget (cell ∷ cells) =
  let
    summed :
      cellCommutatorSquared cell + sumCellCommutatorSquared cells
      ≤ Scale.two * weakCellEnvelope cell
        + Scale.two * sumWeakCellEnvelope cells
    summed =
      ℚₚ.+-mono-≤
        (cellSixThreeBudget cell)
        (finiteSixThreeCommutatorBudget cells)

    targetMeaning :
      Scale.two * weakCellEnvelope cell
        + Scale.two * sumWeakCellEnvelope cells
      ≡ Scale.two
        * (weakCellEnvelope cell + sumWeakCellEnvelope cells)
    targetMeaning =
      solve
        ( weakCellEnvelope cell
        ∷ sumWeakCellEnvelope cells
        ∷ [])
  in
  subst
    (λ upper →
      cellCommutatorSquared cell + sumCellCommutatorSquared cells
      ≤ upper)
    targetMeaning
    summed
