module DASHI.Physics.Closure.NSTriadKNLuoFiniteSixThreeKernelDimensionFreeExact where

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
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- PURPOSE
-- Replace the eight-point Holder theorem and its factor 64 by the exact
-- arbitrary-finite constant-one theorem. For each centered Taylor branch,
--
--   branchL2Squared <= M2Squared * sum_i (a_i b_i)^2,
--
-- hence
--
--   branchL2Squared^3
--     <= M2Squared^3 (sum_i a_i^6) (sum_i b_i^3)^2.
--
-- Combining two nonnegative branches costs only the elementary factor four:
--
--   (B1+B2)^3 <= 4(B1^3+B2^3).
--
-- The result is uniform in the number of quadrature/spatial samples.
--
-- COMPILER NOTE
-- This module needs only elementary ordered-rational positivity/monotonicity.
-- It intentionally imports the tiny FiniteRationalOrderCore rather than the
-- full recursive finite-L2/Gram development.  The constant-one Holder theorem
-- is likewise taken from the compiled-core variant that does not import the
-- legacy recursive Gram proof.  The branch and centered endpoint proofs are
-- abstract so later consumers only elaborate their theorem types.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteRationalOrderCore as Core
import DASHI.Physics.Closure.NSTriadKNLuoFiniteEightPointSixThreeHolderExact as Eight
import DASHI.Physics.Closure.NSTriadKNLuoFiniteSixThreeHolderConstantOneCompiledExact as Holder

record FiniteSixThreeBranchData : Set where
  constructor finite-six-three-branch-data
  field
    holderPairs : List Holder.NonnegativePair
    kernelSecondMomentSquared branchL2Squared : ℚ
    kernelSecondMomentSquaredNonnegative : 0ℚ ≤ kernelSecondMomentSquared
    branchL2SquaredNonnegative : 0ℚ ≤ branchL2Squared
    branchKernelBound :
      branchL2Squared
      ≤ kernelSecondMomentSquared
        * Holder.sumBy Holder.productMass holderPairs

open FiniteSixThreeBranchData public

cubeMonotone :
  ∀ {left right : ℚ} →
  0ℚ ≤ left → left ≤ right →
  Holder.cube left ≤ Holder.cube right
cubeMonotone {left} {right} leftNN left≤right =
  let
    rightNN = ℚₚ.≤-trans leftNN left≤right
    squareBound =
      Core.nonnegativeProductMonotone
        leftNN leftNN rightNN rightNN left≤right left≤right
  in
  Core.nonnegativeProductMonotone
    (Core.squareNonnegative left) leftNN
    (Core.squareNonnegative right) rightNN
    squareBound left≤right

abstract
  branchCubeBound :
    (dataSet : FiniteSixThreeBranchData) →
    Holder.cube (branchL2Squared dataSet)
    ≤ Holder.cube (kernelSecondMomentSquared dataSet)
      * Holder.sumBy Holder.leftSixthMass (holderPairs dataSet)
      * (Holder.sumBy Holder.rightCubeMass (holderPairs dataSet)
        * Holder.sumBy Holder.rightCubeMass (holderPairs dataSet))
  branchCubeBound dataSet =
    let
      monotone :
        Holder.cube (branchL2Squared dataSet)
        ≤ Holder.cube
            (kernelSecondMomentSquared dataSet
              * Holder.sumBy Holder.productMass (holderPairs dataSet))
      monotone =
        cubeMonotone
          (branchL2SquaredNonnegative dataSet)
          (branchKernelBound dataSet)

      holderBound =
        Holder.finiteSixThreeHolderRadicalFree (holderPairs dataSet)

      momentCubeNN :
        0ℚ ≤ Holder.cube (kernelSecondMomentSquared dataSet)
      momentCubeNN =
        Eight.cubeNonnegative
          (kernelSecondMomentSquared dataSet)
          (kernelSecondMomentSquaredNonnegative dataSet)

      scaledHolder :
        Holder.cube (kernelSecondMomentSquared dataSet)
          * Holder.cube (Holder.sumBy Holder.productMass (holderPairs dataSet))
        ≤ Holder.cube (kernelSecondMomentSquared dataSet)
          * (Holder.sumBy Holder.leftSixthMass (holderPairs dataSet)
            * (Holder.sumBy Holder.rightCubeMass (holderPairs dataSet)
              * Holder.sumBy Holder.rightCubeMass (holderPairs dataSet)))
      scaledHolder =
        Eight.scaleBound
          (Holder.cube (kernelSecondMomentSquared dataSet))
          (Holder.cube (Holder.sumBy Holder.productMass (holderPairs dataSet)))
          (Holder.sumBy Holder.leftSixthMass (holderPairs dataSet)
            * (Holder.sumBy Holder.rightCubeMass (holderPairs dataSet)
              * Holder.sumBy Holder.rightCubeMass (holderPairs dataSet)))
          momentCubeNN
          holderBound

      leftMeaning :
        Holder.cube
          (kernelSecondMomentSquared dataSet
            * Holder.sumBy Holder.productMass (holderPairs dataSet))
        ≡ Holder.cube (kernelSecondMomentSquared dataSet)
          * Holder.cube (Holder.sumBy Holder.productMass (holderPairs dataSet))
      leftMeaning = solve
        ( kernelSecondMomentSquared dataSet
        ∷ Holder.sumBy Holder.productMass (holderPairs dataSet)
        ∷ [])

      endpoint :
        Holder.cube (kernelSecondMomentSquared dataSet)
          * (Holder.sumBy Holder.leftSixthMass (holderPairs dataSet)
            * (Holder.sumBy Holder.rightCubeMass (holderPairs dataSet)
              * Holder.sumBy Holder.rightCubeMass (holderPairs dataSet)))
        ≡ Holder.cube (kernelSecondMomentSquared dataSet)
          * Holder.sumBy Holder.leftSixthMass (holderPairs dataSet)
          * (Holder.sumBy Holder.rightCubeMass (holderPairs dataSet)
            * Holder.sumBy Holder.rightCubeMass (holderPairs dataSet))
      endpoint = solve
        ( Holder.cube (kernelSecondMomentSquared dataSet)
        ∷ Holder.sumBy Holder.leftSixthMass (holderPairs dataSet)
        ∷ Holder.sumBy Holder.rightCubeMass (holderPairs dataSet)
        ∷ [])
    in
    ℚₚ.≤-trans
      monotone
      (subst
        (λ lower →
          lower
          ≤ Holder.cube (kernelSecondMomentSquared dataSet)
            * Holder.sumBy Holder.leftSixthMass (holderPairs dataSet)
            * (Holder.sumBy Holder.rightCubeMass (holderPairs dataSet)
              * Holder.sumBy Holder.rightCubeMass (holderPairs dataSet)))
        (sym leftMeaning)
        (subst
          (λ upper →
            Holder.cube (kernelSecondMomentSquared dataSet)
              * Holder.cube (Holder.sumBy Holder.productMass (holderPairs dataSet))
            ≤ upper)
          endpoint
          scaledHolder))

record FiniteCenteredSixThreeData : Set where
  constructor finite-centered-six-three-data
  field
    firstBranch secondBranch : FiniteSixThreeBranchData
    commonKernelMomentMeaning :
      kernelSecondMomentSquared firstBranch
      ≡ kernelSecondMomentSquared secondBranch

open FiniteCenteredSixThreeData public

abstract
  centeredSixThreeKernelDimensionFree :
    (dataSet : FiniteCenteredSixThreeData) →
    Holder.cube
      (branchL2Squared (firstBranch dataSet)
        + branchL2Squared (secondBranch dataSet))
    ≤ Eight.four
      * ( Holder.cube
            (kernelSecondMomentSquared (firstBranch dataSet))
          * Holder.sumBy Holder.leftSixthMass
              (holderPairs (firstBranch dataSet))
          * (Holder.sumBy Holder.rightCubeMass
                (holderPairs (firstBranch dataSet))
            * Holder.sumBy Holder.rightCubeMass
                (holderPairs (firstBranch dataSet)))
        + Holder.cube
            (kernelSecondMomentSquared (secondBranch dataSet))
          * Holder.sumBy Holder.leftSixthMass
              (holderPairs (secondBranch dataSet))
          * (Holder.sumBy Holder.rightCubeMass
                (holderPairs (secondBranch dataSet))
            * Holder.sumBy Holder.rightCubeMass
                (holderPairs (secondBranch dataSet))) )
  centeredSixThreeKernelDimensionFree dataSet =
    let
      pairBound =
        Eight.cubePairBound
          (branchL2Squared (firstBranch dataSet))
          (branchL2Squared (secondBranch dataSet))
          (branchL2SquaredNonnegative (firstBranch dataSet))
          (branchL2SquaredNonnegative (secondBranch dataSet))

      summed =
        ℚₚ.+-mono-≤
          (branchCubeBound (firstBranch dataSet))
          (branchCubeBound (secondBranch dataSet))

      scaled =
        Eight.scaleBound
          Eight.four _ _ Eight.fourNonnegative summed
    in
    ℚₚ.≤-trans pairBound scaled
