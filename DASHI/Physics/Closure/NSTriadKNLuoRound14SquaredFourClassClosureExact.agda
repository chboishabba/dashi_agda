module DASHI.Physics.Closure.NSTriadKNLuoRound14SquaredFourClassClosureExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Jean-Michel Bony; Hajer Bahouri; Jean-Yves Chemin;
-- Raphael Danchin.
-- Bony DOI: 10.24033/asens.1404.
-- Bahouri--Chemin--Danchin DOI: 10.1007/978-3-642-16830-7.
--
-- Authors: Augustin-Louis Cauchy; Hermann Amandus Schwarz.
-- Title: finite Cauchy--Schwarz inequality.
-- DOI: not applicable to the nineteenth-century result.
--
-- PURPOSE
-- Assemble the four terminal interaction classes without taking square roots.
-- The new periodic HH, repaired HL and centered LH modules naturally produce
-- squared estimates.  For four signed class interactions a,b,c,d,
--
--   (a+b+c+d)^2 <= 4 (a^2+b^2+c^2+d^2).
--
-- Combining this finite Cauchy estimate with the four classwise squared
-- envelopes gives
--
--   N_q^2 <= 4 C_sum A_q^2 E_q^2.
--
-- This is the exact radical-free counterpart of the usual unsquared
-- four-class criterion and avoids silently extracting rational square roots.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
import Data.Integer.Base as Int
open import Data.Product.Base using (_,_)
open import Data.Rational.Base using (ℚ; 0ℚ; _/_; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

four : ℚ
four = Int.+ 4 / 1

record SquaredFourClassBudget : Set where
  constructor squared-four-class-budget
  field
    lowHigh highLow comparable highHighToLow : ℚ
    lowHighCoefficient highLowCoefficient : ℚ
    comparableCoefficient highHighToLowCoefficient : ℚ
    criticalEnvelopeSquared outputEnvelopeSquared : ℚ

    lowHighSquareBound :
      L2.square lowHigh
      ≤ lowHighCoefficient
        * criticalEnvelopeSquared * outputEnvelopeSquared

    highLowSquareBound :
      L2.square highLow
      ≤ highLowCoefficient
        * criticalEnvelopeSquared * outputEnvelopeSquared

    comparableSquareBound :
      L2.square comparable
      ≤ comparableCoefficient
        * criticalEnvelopeSquared * outputEnvelopeSquared

    highHighToLowSquareBound :
      L2.square highHighToLow
      ≤ highHighToLowCoefficient
        * criticalEnvelopeSquared * outputEnvelopeSquared

open SquaredFourClassBudget public

totalInteraction : SquaredFourClassBudget → ℚ
totalInteraction budget =
  lowHigh budget + highLow budget
  + comparable budget + highHighToLow budget

coefficientSum : SquaredFourClassBudget → ℚ
coefficientSum budget =
  lowHighCoefficient budget + highLowCoefficient budget
  + comparableCoefficient budget + highHighToLowCoefficient budget

classPairs : SquaredFourClassBudget → List L2.Pair
classPairs budget =
  (lowHigh budget , Int.+ 1 / 1)
  ∷ (highLow budget , Int.+ 1 / 1)
  ∷ (comparable budget , Int.+ 1 / 1)
  ∷ (highHighToLow budget , Int.+ 1 / 1)
  ∷ []

classPairDotMeaning :
  (budget : SquaredFourClassBudget) →
  L2.pairDot (classPairs budget) ≡ totalInteraction budget
classPairDotMeaning budget = solve []

classLeftNormMeaning :
  (budget : SquaredFourClassBudget) →
  L2.leftNormSquared (classPairs budget)
  ≡ L2.square (lowHigh budget)
    + L2.square (highLow budget)
    + L2.square (comparable budget)
    + L2.square (highHighToLow budget)
classLeftNormMeaning budget = solve []

classRightNormMeaning :
  (budget : SquaredFourClassBudget) →
  L2.rightNormSquared (classPairs budget) ≡ four
classRightNormMeaning budget = solve []

classSquareSumBound :
  (budget : SquaredFourClassBudget) →
  L2.square (lowHigh budget)
    + L2.square (highLow budget)
    + L2.square (comparable budget)
    + L2.square (highHighToLow budget)
  ≤ coefficientSum budget
      * criticalEnvelopeSquared budget
      * outputEnvelopeSquared budget
classSquareSumBound budget =
  let
    summed :
      L2.square (lowHigh budget)
        + L2.square (highLow budget)
        + L2.square (comparable budget)
        + L2.square (highHighToLow budget)
      ≤ (lowHighCoefficient budget
          * criticalEnvelopeSquared budget
          * outputEnvelopeSquared budget)
        + (highLowCoefficient budget
          * criticalEnvelopeSquared budget
          * outputEnvelopeSquared budget)
        + (comparableCoefficient budget
          * criticalEnvelopeSquared budget
          * outputEnvelopeSquared budget)
        + (highHighToLowCoefficient budget
          * criticalEnvelopeSquared budget
          * outputEnvelopeSquared budget)
    summed =
      ℚₚ.+-mono-≤
        (ℚₚ.+-mono-≤
          (ℚₚ.+-mono-≤
            (lowHighSquareBound budget)
            (highLowSquareBound budget))
          (comparableSquareBound budget))
        (highHighToLowSquareBound budget)

    targetMeaning :
      (lowHighCoefficient budget
          * criticalEnvelopeSquared budget
          * outputEnvelopeSquared budget)
        + (highLowCoefficient budget
          * criticalEnvelopeSquared budget
          * outputEnvelopeSquared budget)
        + (comparableCoefficient budget
          * criticalEnvelopeSquared budget
          * outputEnvelopeSquared budget)
        + (highHighToLowCoefficient budget
          * criticalEnvelopeSquared budget
          * outputEnvelopeSquared budget)
      ≡ coefficientSum budget
          * criticalEnvelopeSquared budget
          * outputEnvelopeSquared budget
    targetMeaning =
      solve
        ( lowHighCoefficient budget
        ∷ highLowCoefficient budget
        ∷ comparableCoefficient budget
        ∷ highHighToLowCoefficient budget
        ∷ criticalEnvelopeSquared budget
        ∷ outputEnvelopeSquared budget
        ∷ [])
  in
  subst
    (λ upper →
      L2.square (lowHigh budget)
        + L2.square (highLow budget)
        + L2.square (comparable budget)
        + L2.square (highHighToLow budget)
      ≤ upper)
    targetMeaning
    summed

squaredFourClassTerminalAssembly :
  (budget : SquaredFourClassBudget) →
  L2.square (totalInteraction budget)
  ≤ four *
      (coefficientSum budget
        * criticalEnvelopeSquared budget
        * outputEnvelopeSquared budget)
squaredFourClassTerminalAssembly budget =
  let
    cauchy :
      L2.square (L2.pairDot (classPairs budget))
      ≤ L2.leftNormSquared (classPairs budget)
        * L2.rightNormSquared (classPairs budget)
    cauchy = L2.finiteCauchySchwarzSquared (classPairs budget)

    normalizedCauchy :
      L2.square (totalInteraction budget)
      ≤ four *
        (L2.square (lowHigh budget)
          + L2.square (highLow budget)
          + L2.square (comparable budget)
          + L2.square (highHighToLow budget))
    normalizedCauchy =
      let
        dotAdjusted :
          L2.square (totalInteraction budget)
          ≤ L2.leftNormSquared (classPairs budget)
            * L2.rightNormSquared (classPairs budget)
        dotAdjusted =
          subst
            (λ dotValue →
              L2.square dotValue
              ≤ L2.leftNormSquared (classPairs budget)
                * L2.rightNormSquared (classPairs budget))
            (classPairDotMeaning budget)
            cauchy

        leftAdjusted :
          L2.square (totalInteraction budget)
          ≤ (L2.square (lowHigh budget)
              + L2.square (highLow budget)
              + L2.square (comparable budget)
              + L2.square (highHighToLow budget))
            * L2.rightNormSquared (classPairs budget)
        leftAdjusted =
          subst
            (λ leftNorm →
              L2.square (totalInteraction budget)
              ≤ leftNorm * L2.rightNormSquared (classPairs budget))
            (classLeftNormMeaning budget)
            dotAdjusted

        rightAdjusted :
          L2.square (totalInteraction budget)
          ≤ (L2.square (lowHigh budget)
              + L2.square (highLow budget)
              + L2.square (comparable budget)
              + L2.square (highHighToLow budget))
            * four
        rightAdjusted =
          subst
            (λ rightNorm →
              L2.square (totalInteraction budget)
              ≤ (L2.square (lowHigh budget)
                  + L2.square (highLow budget)
                  + L2.square (comparable budget)
                  + L2.square (highHighToLow budget))
                * rightNorm)
            (classRightNormMeaning budget)
            leftAdjusted

        commuted :
          (L2.square (lowHigh budget)
              + L2.square (highLow budget)
              + L2.square (comparable budget)
              + L2.square (highHighToLow budget))
            * four
          ≡ four *
            (L2.square (lowHigh budget)
              + L2.square (highLow budget)
              + L2.square (comparable budget)
              + L2.square (highHighToLow budget))
        commuted = solve
          ( L2.square (lowHigh budget)
            + L2.square (highLow budget)
            + L2.square (comparable budget)
            + L2.square (highHighToLow budget)
          ∷ [])
      in
      subst
        (λ upper → L2.square (totalInteraction budget) ≤ upper)
        commuted
        rightAdjusted

    scaledClassBound :
      four *
        (L2.square (lowHigh budget)
          + L2.square (highLow budget)
          + L2.square (comparable budget)
          + L2.square (highHighToLow budget))
      ≤ four *
        (coefficientSum budget
          * criticalEnvelopeSquared budget
          * outputEnvelopeSquared budget)
    scaledClassBound =
      let
        fourNonnegative : 0ℚ ≤ four
        fourNonnegative = L2.squareNonnegative (Int.+ 2 / 1)
        instance
          fourIsNonnegative = nonNegative fourNonnegative
      in
      ℚₚ.*-monoˡ-≤-nonNeg four (classSquareSumBound budget)
  in
  ℚₚ.≤-trans normalizedCauchy scaledClassBound
