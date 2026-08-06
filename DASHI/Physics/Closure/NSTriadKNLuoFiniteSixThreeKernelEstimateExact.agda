module DASHI.Physics.Closure.NSTriadKNLuoFiniteSixThreeKernelEstimateExact where

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
-- PURPOSE
-- Combine the centered two-branch identity, a finite second-moment kernel
-- bound, and the concrete eight-point (L6,L3)->L2 theorem. To avoid roots,
-- the result is stated at the sixth-power level. If each branch satisfies
--
--   branchL2^2 <= M2^2 productL2^2,
--
-- then the complete centered commutator satisfies an explicit bound with no
-- unproved Holder field.
------------------------------------------------------------------------

open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoFiniteEightPointSixThreeHolderExact as Holder

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
      L2.nonnegativeProductMonotone
        leftNN leftNN rightNN rightNN left≤right left≤right
  in
  L2.nonnegativeProductMonotone
    (L2.squareNonnegative left) leftNN
    (L2.squareNonnegative right) rightNN
    squareBound left≤right

productL2SquaredNonnegative :
  (dataSet : Holder.EightSixThreeData) →
  0ℚ ≤ Holder.productL2Squared dataSet
productL2SquaredNonnegative dataSet =
  L2.addNonnegative
    (L2.addNonnegative
      (L2.addNonnegative
        (L2.addNonnegative
          (L2.addNonnegative
            (L2.addNonnegative
              (L2.addNonnegative
                (L2.squareNonnegative
                  (Holder.a0 dataSet * Holder.b0 dataSet))
                (L2.squareNonnegative
                  (Holder.a1 dataSet * Holder.b1 dataSet)))
              (L2.squareNonnegative
                (Holder.a2 dataSet * Holder.b2 dataSet)))
            (L2.squareNonnegative
              (Holder.a3 dataSet * Holder.b3 dataSet)))
          (L2.squareNonnegative
            (Holder.a4 dataSet * Holder.b4 dataSet)))
        (L2.squareNonnegative
          (Holder.a5 dataSet * Holder.b5 dataSet)))
      (L2.squareNonnegative
        (Holder.a6 dataSet * Holder.b6 dataSet)))
    (L2.squareNonnegative
      (Holder.a7 dataSet * Holder.b7 dataSet))

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
    leftMeaning = solve
      (momentSquared ∷ Holder.productL2Squared holderData ∷ [])

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
    endpoint = solve
      ( Holder.cube momentSquared
      ∷ Holder.lowSixthMass holderData
      ∷ Holder.highCubeMass holderData
      ∷ [])
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

centeredSixThreeKernelSixthPowerBound :
  (dataSet : FiniteSixThreeKernelData) →
  Holder.cube
    (firstBranchL2Squared dataSet + secondBranchL2Squared dataSet)
  ≤ (Holder.four * Holder.sixtyFour)
    * Holder.cube (kernelSecondMomentSquared dataSet)
    * ( Holder.lowSixthMass (firstHolder dataSet)
        * (Holder.highCubeMass (firstHolder dataSet)
          * Holder.highCubeMass (firstHolder dataSet))
      + Holder.lowSixthMass (secondHolder dataSet)
        * (Holder.highCubeMass (secondHolder dataSet)
          * Holder.highCubeMass (secondHolder dataSet)))
centeredSixThreeKernelSixthPowerBound dataSet =
  let
    pairBound =
      Holder.cubePairBound
        (firstBranchL2Squared dataSet)
        (secondBranchL2Squared dataSet)
        (firstBranchNonnegative dataSet)
        (secondBranchNonnegative dataSet)

    first = branchCubeBound
      (firstHolder dataSet)
      (kernelSecondMomentSquared dataSet)
      (firstBranchL2Squared dataSet)
      (kernelSecondMomentSquaredNonnegative dataSet)
      (firstBranchNonnegative dataSet)
      (firstKernelBound dataSet)

    second = branchCubeBound
      (secondHolder dataSet)
      (kernelSecondMomentSquared dataSet)
      (secondBranchL2Squared dataSet)
      (kernelSecondMomentSquaredNonnegative dataSet)
      (secondBranchNonnegative dataSet)
      (secondKernelBound dataSet)

    summed = ℚₚ.+-mono-≤ first second

    scaled = Holder.scaleBound
      Holder.four _ _ Holder.fourNonnegative summed

    endpoint = solve
      ( Holder.cube (kernelSecondMomentSquared dataSet)
      ∷ Holder.lowSixthMass (firstHolder dataSet)
      ∷ Holder.highCubeMass (firstHolder dataSet)
      ∷ Holder.lowSixthMass (secondHolder dataSet)
      ∷ Holder.highCubeMass (secondHolder dataSet)
      ∷ [])
  in
  ℚₚ.≤-trans
    pairBound
    (subst
      (λ upper →
        Holder.four
          * (Holder.cube (firstBranchL2Squared dataSet)
            + Holder.cube (secondBranchL2Squared dataSet))
        ≤ upper)
      endpoint
      scaled)
