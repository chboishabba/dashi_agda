module DASHI.Physics.YangMills.BalabanClayStrictMacrostepComponentAssemblyExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. II. Localization, Exponentiation, and Bounds
-- for the R Operation", Communications in Mathematical Physics 122 (1989),
-- 355--392. DOI: 10.1007/BF01238433.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- DASHI CONTRIBUTION
--
-- The existing all-scale RG induction accepted the complete one-step polymer
-- inequality as one field.  This file decomposes that field into the five
-- actual mechanisms named by the Clay roadmap:
--
--   linear, fluctuation, localization, large-field, boundary.
--
-- With the explicit allocations
--
--   1/4 + 1/8 + 1/16 + 1/16 = 1/2,
--
-- finite monotonicity proves
--
--   ||K'|| <= (1/2)||K|| + perturbativeError.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; -_; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

linearFraction localizationFraction largeFieldFraction boundaryFraction : ℚ
linearFraction = + 1 / 4
localizationFraction = + 1 / 8
largeFieldFraction = + 1 / 16
boundaryFraction = + 1 / 16

strictContraction : ℚ
strictContraction = + 1 / 2

fourContractiveFractionsSumExactly :
  linearFraction
  + (localizationFraction + (largeFieldFraction + boundaryFraction))
  ≡ strictContraction
fourContractiveFractionsSumExactly = ℚRing.solve []

record FiveMechanismMacrostep : Set₁ where
  field
    currentNorm nextNorm : ℚ
    linearPart fluctuationPart localizationPart
      largeFieldPart boundaryPart : ℚ
    perturbativeError : ℚ

    nextNormDecomposition :
      nextNorm
      ≡ linearPart
        + (fluctuationPart
          + (localizationPart + (largeFieldPart + boundaryPart)))

    linearBound : linearPart ≤ linearFraction * currentNorm
    fluctuationBound : fluctuationPart ≤ perturbativeError
    localizationBound :
      localizationPart ≤ localizationFraction * currentNorm
    largeFieldBound :
      largeFieldPart ≤ largeFieldFraction * currentNorm
    boundaryBound :
      boundaryPart ≤ boundaryFraction * currentNorm

open FiveMechanismMacrostep public

strictMacrostepFromFiveMechanisms :
  (dataSet : FiveMechanismMacrostep) →
  nextNorm dataSet
  ≤ strictContraction * currentNorm dataSet
    + perturbativeError dataSet
strictMacrostepFromFiveMechanisms dataSet =
  subst
    (λ lower → lower
      ≤ strictContraction * currentNorm dataSet
        + perturbativeError dataSet)
    (sym (nextNormDecomposition dataSet))
    (ℚP.≤-trans
      (ℚP.+-mono-≤
        (linearBound dataSet)
        (ℚP.+-mono-≤
          (fluctuationBound dataSet)
          (ℚP.+-mono-≤
            (localizationBound dataSet)
            (ℚP.+-mono-≤
              (largeFieldBound dataSet)
              (boundaryBound dataSet)))))
      (subst
        (λ upper →
          linearFraction * currentNorm dataSet
          + (perturbativeError dataSet
            + (localizationFraction * currentNorm dataSet
              + (largeFieldFraction * currentNorm dataSet
                + boundaryFraction * currentNorm dataSet)))
          ≤ upper)
        (ℚRing.solve-∀
          (currentNorm dataSet) (perturbativeError dataSet))
        ℚP.≤-refl))

------------------------------------------------------------------------
-- Large-field exponent calibration from the physical Hessian floor.
------------------------------------------------------------------------

hessianFloor halfGaussianFloor retainedGaussianFloor : ℚ
hessianFloor = + 1 / 32
halfGaussianFloor = + 1 / 64
retainedGaussianFloor = + 1 / 128

halfOfHessianFloorExact :
  (+ 1 / 2) * hessianFloor ≡ halfGaussianFloor
halfOfHessianFloorExact = ℚRing.solve []

record LargeFieldAbsorption : Set where
  field
    normSq quadraticEnergy interactionAbs : ℚ
    normSqNonnegative : 0ℚ ≤ normSq
    hessianFloorBound : hessianFloor * normSq ≤ quadraticEnergy
    interactionAbsorbed : interactionAbs ≤ (+ 1 / 4) * quadraticEnergy

open LargeFieldAbsorption public

retainedQuadraticExponent : LargeFieldAbsorption → ℚ
retainedQuadraticExponent dataSet =
  (+ 1 / 2) * quadraticEnergy dataSet - interactionAbs dataSet

scaledHessianFloorIsRetainedFloor : ∀ normValue →
  (+ 1 / 4) * (hessianFloor * normValue)
  ≡ retainedGaussianFloor * normValue
scaledHessianFloorIsRetainedFloor = ℚRing.solve-∀

halfPlusNegativeQuarterIsQuarter : ∀ energy →
  (+ 1 / 2) * energy + (- ((+ 1 / 4) * energy))
  ≡ (+ 1 / 4) * energy
halfPlusNegativeQuarterIsQuarter = ℚRing.solve-∀

halfPlusNegativeInteractionIsRetained : ∀ energy interaction →
  (+ 1 / 2) * energy + (- interaction)
  ≡ (+ 1 / 2) * energy - interaction
halfPlusNegativeInteractionIsRetained = ℚRing.solve-∀

quarterEnergyBelowRetainedExponent :
  (dataSet : LargeFieldAbsorption) →
  (+ 1 / 4) * quadraticEnergy dataSet
  ≤ retainedQuadraticExponent dataSet
quarterEnergyBelowRetainedExponent dataSet =
  let
    shifted :
      (+ 1 / 2) * quadraticEnergy dataSet
        + (- ((+ 1 / 4) * quadraticEnergy dataSet))
      ≤ (+ 1 / 2) * quadraticEnergy dataSet
        + (- interactionAbs dataSet)
    shifted =
      ℚP.+-mono-≤
        ℚP.≤-refl
        (ℚP.neg-mono-≤ (interactionAbsorbed dataSet))
  in
  subst
    (λ lower → lower ≤ retainedQuadraticExponent dataSet)
    (halfPlusNegativeQuarterIsQuarter (quadraticEnergy dataSet))
    (subst
      (λ upper →
        (+ 1 / 2) * quadraticEnergy dataSet
          + (- ((+ 1 / 4) * quadraticEnergy dataSet))
        ≤ upper)
      (halfPlusNegativeInteractionIsRetained
        (quadraticEnergy dataSet) (interactionAbs dataSet))
      shifted)

largeFieldLeavesPositiveGaussian :
  (dataSet : LargeFieldAbsorption) →
  retainedGaussianFloor * normSq dataSet
  ≤ retainedQuadraticExponent dataSet
largeFieldLeavesPositiveGaussian dataSet =
  ℚP.≤-trans
    (subst
      (λ lower → lower ≤ (+ 1 / 4) * quadraticEnergy dataSet)
      (scaledHessianFloorIsRetainedFloor (normSq dataSet))
      (ℚP.*-monoˡ-≤-nonNeg (+ 1 / 4)
        (hessianFloorBound dataSet)))
    (quarterEnergyBelowRetainedExponent dataSet)

strictMacrostepAssemblyLevel : ProofLevel
strictMacrostepAssemblyLevel = machineChecked

largeFieldAbsorptionArithmeticLevel : ProofLevel
largeFieldAbsorptionArithmeticLevel = machineChecked

physicalFiveMechanismProducerLevel : ProofLevel
physicalFiveMechanismProducerLevel = conditional
