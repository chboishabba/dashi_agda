module DASHI.Physics.Closure.NSTriadKNLuoFiniteTensorHolderExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Augustin-Louis Cauchy; Hermann Amandus Schwarz.
-- Title: finite Cauchy--Schwarz inequality.
-- DOI: not applicable to the nineteenth-century result.
--
-- Harmonic-analysis reference:
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- PURPOSE
-- Instantiate the tensor Holder step used in HH1.  For finite nonnegative
-- pointwise magnitudes f_i,g_i,
--
--   (sum_i f_i g_i)^2
--     <= (sum_i f_i^2) (sum_i g_i^2).
--
-- This is exactly ||f tensor g||_1^2 <= ||f||_2^2 ||g||_2^2 on the finite
-- rational carrier.  The proof reuses the repository's full Gram-defect
-- identity rather than accepting Holder as an input field.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.List.Base using (List)
open import Data.Rational.Base using (ℚ; _≤_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

record FiniteTensorHolderData : Set where
  constructor finite-tensor-holder-data
  field
    pointwisePairs : List L2.Pair
    tensorL1Squared leftL2Squared rightL2Squared : ℚ

    tensorMeaning :
      tensorL1Squared ≡ L2.square (L2.pairDot pointwisePairs)

    leftNormMeaning :
      leftL2Squared ≡ L2.leftNormSquared pointwisePairs

    rightNormMeaning :
      rightL2Squared ≡ L2.rightNormSquared pointwisePairs

open FiniteTensorHolderData public

finiteTensorHolderSquare :
  (dataSet : FiniteTensorHolderData) →
  tensorL1Squared dataSet
  ≤ leftL2Squared dataSet * rightL2Squared dataSet
finiteTensorHolderSquare dataSet =
  let
    cauchy :
      L2.square (L2.pairDot (pointwisePairs dataSet))
      ≤ L2.leftNormSquared (pointwisePairs dataSet)
        * L2.rightNormSquared (pointwisePairs dataSet)
    cauchy = L2.finiteCauchySchwarzSquared (pointwisePairs dataSet)

    rightAdjusted :
      L2.square (L2.pairDot (pointwisePairs dataSet))
      ≤ L2.leftNormSquared (pointwisePairs dataSet)
        * rightL2Squared dataSet
    rightAdjusted =
      subst
        (λ rightNorm →
          L2.square (L2.pairDot (pointwisePairs dataSet))
          ≤ L2.leftNormSquared (pointwisePairs dataSet) * rightNorm)
        (sym (rightNormMeaning dataSet))
        cauchy

    bothAdjusted :
      L2.square (L2.pairDot (pointwisePairs dataSet))
      ≤ leftL2Squared dataSet * rightL2Squared dataSet
    bothAdjusted =
      subst
        (λ leftNorm →
          L2.square (L2.pairDot (pointwisePairs dataSet))
          ≤ leftNorm * rightL2Squared dataSet)
        (sym (leftNormMeaning dataSet))
        rightAdjusted
  in
  subst
    (λ lower →
      lower ≤ leftL2Squared dataSet * rightL2Squared dataSet)
    (sym (tensorMeaning dataSet))
    bothAdjusted
