module DASHI.Physics.Closure.NSTriadKNLuoFiniteSixThreeKernelBranchBoundary where

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
-- Authors: Francesca Da Lio; Tristan Rivière.
-- Title: "Three-Term Commutator Estimates and the Regularity of
-- 1/2-Harmonic Maps into Spheres".
-- DOI: 10.2140/apde.2011.4.149.
--
-- COMPILER BOUNDARY
--
-- The legacy six-three kernel consumer only needs three elementary rational
-- positivity facts plus the already-compiled eight-point Hölder theorem.  It
-- historically imported NSTriadKNRationalOrderedFiniteL2, whose recursive
-- Gram/Cauchy--Schwarz development is unrelated to this branch estimate and
-- was a major elaboration dependency.
--
-- This module is the exact cut:
--   source record
--   + cube monotonicity
--   + positivity of the concrete eight-term product L2 mass
--   + one-branch sixth-power estimate.
--
-- The centered two-branch assembly lives downstream.  The branch theorem is
-- abstract so importing its statement does not unfold its proof body.
------------------------------------------------------------------------

open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _*_; _≤_)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteRationalOrderCore as Core
import DASHI.Physics.Closure.NSTriadKNLuoFiniteEightPointSixThreeHolderExact as Holder

cubeProductMeaning :
  (x y : ℚ) →
  Holder.cube (x * y) ≡ Holder.cube x * Holder.cube y
cubeProductMeaning x y
  rewrite Holder.cubeMeaning (x * y)
        | Holder.cubeMeaning x
        | Holder.cubeMeaning y
  = solve (x ∷ y ∷ [])

endpointReassociate :
  (x y z : ℚ) →
  Holder.cube x
    * (Holder.sixtyFour * y * (z * z))
    ≡ Holder.sixtyFour * Holder.cube x * y * (z * z)
endpointReassociate x y z
  rewrite Holder.cubeMeaning x | Holder.sixtyFourMeaning
  = solve (x ∷ y ∷ z ∷ [])

record FiniteSixThreeKernelData : Set where
  constructor finite-six-three-kernel-data
  field
    firstHolder secondHolder : Holder.EightSixThreeData
    kernelSecondMomentSquared : ℚ
    firstBranchL2Squared secondBranchL2Squared : ℚ

    kernelSecondMomentSquaredNonnegative : 0ℚ ≤ kernelSecondMomentSquared
    firstBranchNonnegative : 0ℚ ≤ firstBranchL2Squared
    secondBranchNonnegative : 0ℚ ≤ secondBranchL2Squared

    firstKernelBound :
      firstBranchL2Squared
      ≤ kernelSecondMomentSquared * Holder.productL2Squared firstHolder

    secondKernelBound :
      secondBranchL2Squared
      ≤ kernelSecondMomentSquared * Holder.productL2Squared secondHolder

open FiniteSixThreeKernelData public

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

productL2SquaredNonnegative :
  (dataSet : Holder.EightSixThreeData) →
  0ℚ ≤ Holder.productL2Squared dataSet
productL2SquaredNonnegative dataSet =
  Core.addNonnegative
    (Core.addNonnegative
      (Core.addNonnegative
        (Core.addNonnegative
          (Core.addNonnegative
            (Core.addNonnegative
              (Core.addNonnegative
                (Core.squareNonnegative
                  (Holder.a0 dataSet * Holder.b0 dataSet))
                (Core.squareNonnegative
                  (Holder.a1 dataSet * Holder.b1 dataSet)))
              (Core.squareNonnegative
                (Holder.a2 dataSet * Holder.b2 dataSet)))
            (Core.squareNonnegative
              (Holder.a3 dataSet * Holder.b3 dataSet)))
          (Core.squareNonnegative
            (Holder.a4 dataSet * Holder.b4 dataSet)))
        (Core.squareNonnegative
          (Holder.a5 dataSet * Holder.b5 dataSet)))
      (Core.squareNonnegative
        (Holder.a6 dataSet * Holder.b6 dataSet)))
    (Core.squareNonnegative
      (Holder.a7 dataSet * Holder.b7 dataSet))

abstract
  branchCubeBound :
    (holderData : Holder.EightSixThreeData) →
    (momentSquared branchSquared : ℚ) →
    0ℚ ≤ momentSquared →
    0ℚ ≤ branchSquared →
    branchSquared ≤ momentSquared * Holder.productL2Squared holderData →
    Holder.cube branchSquared
    ≤ Holder.sixtyFour
      * Holder.cube momentSquared
      * Holder.lowSixthMass holderData
      * (Holder.highCubeMass holderData * Holder.highCubeMass holderData)
  branchCubeBound holderData momentSquared branchSquared
    momentNN branchNN branchBound =
    let
      monotone :
        Holder.cube branchSquared
        ≤ Holder.cube
            (momentSquared * Holder.productL2Squared holderData)
      monotone = cubeMonotone branchNN branchBound

      holderBound =
        Holder.eightPointSixThreeHolderRadicalFree holderData

      momentCubeNN = Holder.cubeNonnegative momentSquared momentNN

      scaledHolder :
        Holder.cube momentSquared
          * Holder.cube (Holder.productL2Squared holderData)
        ≤ Holder.cube momentSquared
          * (Holder.sixtyFour
            * Holder.lowSixthMass holderData
            * (Holder.highCubeMass holderData
              * Holder.highCubeMass holderData))
      scaledHolder =
        Holder.scaleBound
          (Holder.cube momentSquared)
          (Holder.cube (Holder.productL2Squared holderData))
          (Holder.sixtyFour
            * Holder.lowSixthMass holderData
            * (Holder.highCubeMass holderData
              * Holder.highCubeMass holderData))
          momentCubeNN
          holderBound

      leftMeaning :
        Holder.cube
          (momentSquared * Holder.productL2Squared holderData)
        ≡ Holder.cube momentSquared
          * Holder.cube (Holder.productL2Squared holderData)
      leftMeaning = cubeProductMeaning
        momentSquared
        (Holder.productL2Squared holderData)

      endpoint :
        Holder.cube momentSquared
          * (Holder.sixtyFour
            * Holder.lowSixthMass holderData
            * (Holder.highCubeMass holderData
              * Holder.highCubeMass holderData))
        ≡ Holder.sixtyFour
          * Holder.cube momentSquared
          * Holder.lowSixthMass holderData
          * (Holder.highCubeMass holderData
            * Holder.highCubeMass holderData)
      endpoint = endpointReassociate
        momentSquared
        (Holder.lowSixthMass holderData)
        (Holder.highCubeMass holderData)
    in
    ℚₚ.≤-trans
      monotone
      (subst
        (λ lower →
          lower
          ≤ Holder.sixtyFour
            * Holder.cube momentSquared
            * Holder.lowSixthMass holderData
            * (Holder.highCubeMass holderData
              * Holder.highCubeMass holderData))
        (sym leftMeaning)
        (subst
          (λ upper →
            Holder.cube momentSquared
              * Holder.cube (Holder.productL2Squared holderData)
            ≤ upper)
          endpoint
          scaledHolder))
