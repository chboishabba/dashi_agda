module DASHI.Physics.Closure.NSTriadKNLuoFiniteCenteredDifferenceSixThreeExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Peter Constantin; Weinan E; Edriss S. Titi.
-- Title: "Onsager's Conjecture on the Energy Conservation for Solutions of
-- Euler's Equation".
-- DOI: 10.1007/BF02099744.
--
-- Author: Piero D'Ancona.
-- Title: "A Short Proof of Commutator Estimates".
-- DOI: 10.1007/s00041-018-9612-8.
-- Correction DOI: 10.1007/s00041-019-09724-7.
--
-- PURPOSE
-- Construct, rather than request, the finite centered-difference branch
-- masses used by the (L6,L3) commutator estimate. The first list represents
--
--   |delta_y^2 a| times |grad g|,
--
-- and the second represents
--
--   |delta_y a| times |delta_y grad g|.
--
-- Given one nonnegative squared kernel second moment M2Squared, define each
-- branch mass exactly as
--
--   M2Squared * sum_i (a_i b_i)^2.
--
-- The explicit nested-sum dimension-free Holder theorem then yields the
-- complete two-branch sixth-power estimate with no branch-bound producer and
-- no cardinality constant.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoFiniteSixThreeHolderConstantOneV2Exact as Holder
import DASHI.Physics.Closure.NSTriadKNLuoFiniteSixThreeKernelDimensionFreeExact as Kernel

sumProductMassNonnegative :
  (pairs : List Holder.NonnegativePair) →
  0ℚ ≤ Holder.sumBy Holder.productMass pairs
sumProductMassNonnegative [] = ℚₚ.≤-refl
sumProductMassNonnegative (pair ∷ pairs) =
  L2.addNonnegative
    (L2.squareNonnegative (Holder.left pair * Holder.right pair))
    (sumProductMassNonnegative pairs)

record CenteredDifferenceSixThreeData : Set where
  constructor centered-difference-six-three-data
  field
    firstDifferencePairs secondDifferencePairs :
      List Holder.NonnegativePair
    kernelSecondMomentSquared : ℚ
    kernelSecondMomentSquaredNonnegative :
      0ℚ ≤ kernelSecondMomentSquared

open CenteredDifferenceSixThreeData public

branchMass :
  ℚ → List Holder.NonnegativePair → ℚ
branchMass momentSquared pairs =
  momentSquared * Holder.sumBy Holder.productMass pairs

branchMassNonnegative :
  (momentSquared : ℚ) →
  (pairs : List Holder.NonnegativePair) →
  0ℚ ≤ momentSquared →
  0ℚ ≤ branchMass momentSquared pairs
branchMassNonnegative momentSquared pairs momentNN =
  let
    pairMassNN = sumProductMassNonnegative pairs
    instance
      momentNNI = nonNegative momentNN
      pairMassNNI = nonNegative pairMassNN
      productNN =
        ℚₚ.nonNeg*nonNeg⇒nonNeg
          momentSquared
          (Holder.sumBy Holder.productMass pairs)
  in
  ℚₚ.nonNegative⁻¹ (branchMass momentSquared pairs)

branchData :
  (momentSquared : ℚ) →
  0ℚ ≤ momentSquared →
  List Holder.NonnegativePair →
  Kernel.FiniteSixThreeBranchData
branchData momentSquared momentNN pairs =
  Kernel.finite-six-three-branch-data
    pairs
    momentSquared
    (branchMass momentSquared pairs)
    momentNN
    (branchMassNonnegative momentSquared pairs momentNN)
    ℚₚ.≤-refl

centeredKernelData :
  CenteredDifferenceSixThreeData →
  Kernel.FiniteCenteredSixThreeData
centeredKernelData dataSet =
  Kernel.finite-centered-six-three-data
    (branchData
      (kernelSecondMomentSquared dataSet)
      (kernelSecondMomentSquaredNonnegative dataSet)
      (firstDifferencePairs dataSet))
    (branchData
      (kernelSecondMomentSquared dataSet)
      (kernelSecondMomentSquaredNonnegative dataSet)
      (secondDifferencePairs dataSet))
    refl
