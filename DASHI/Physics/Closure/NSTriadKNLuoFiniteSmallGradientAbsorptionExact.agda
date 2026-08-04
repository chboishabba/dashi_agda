module DASHI.Physics.Closure.NSTriadKNLuoFiniteSmallGradientAbsorptionExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Authors: Loukas Grafakos; Rodolfo H. Torres.
-- Title: "A Multilinear Schur Test and Multiplier Operators".
-- Journal of Functional Analysis 187 (2001), 1--24.
-- DOI: 10.1006/jfan.2001.3804.
--
-- PURPOSE
-- Prove the explicit finite small-gradient absorption step.  If
--
--   G <= epsilon,
--   (512/93) epsilon <= theta,
--   W >= 0,
--
-- then the four-piece finite Section-4 interaction obeys
--
--   J_total <= theta W.
--
-- This is the ordered-field absorption argument with the exact Schur
-- constant.  It is not a semantic receipt for an already-assumed total bound.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using ([]; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open ℚₚ using (_≤?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteFourInteractionSchurBoundsExact as Four

section4AggregateConstantNonnegative :
  0ℚ ≤ Four.section4AggregateConstant
section4AggregateConstantNonnegative =
  toWitness {a? = 0ℚ ≤? Four.section4AggregateConstant} _

smallGradientAbsorption :
  ∀ gradient energy smallness absorptionCoefficient →
  0ℚ ≤ energy →
  gradient ≤ smallness →
  Four.section4AggregateConstant * smallness
    ≤ absorptionCoefficient →
  Four.section4AggregateConstant * (gradient * energy)
    ≤ absorptionCoefficient * energy
smallGradientAbsorption
  gradient energy smallness absorptionCoefficient
  energyNonnegative gradientBelowSmallness coefficientSmall =
  let
    gradientEnergyBelow :
      gradient * energy ≤ smallness * energy
    gradientEnergyBelow =
      let
        instance
          energyIsNonnegative = nonNegative energyNonnegative
      in
      ℚₚ.*-monoʳ-≤-nonNeg energy gradientBelowSmallness

    scaledGradientEnergyBelow :
      Four.section4AggregateConstant * (gradient * energy)
      ≤ Four.section4AggregateConstant * (smallness * energy)
    scaledGradientEnergyBelow =
      let
        instance
          aggregateConstantIsNonnegative =
            nonNegative section4AggregateConstantNonnegative
      in
      ℚₚ.*-monoˡ-≤-nonNeg
        Four.section4AggregateConstant
        gradientEnergyBelow

    reassociateUpper :
      Four.section4AggregateConstant * (smallness * energy)
      ≡ (Four.section4AggregateConstant * smallness) * energy
    reassociateUpper =
      solve
        (smallness ∷ energy ∷ [])

    toCoefficientTimesEnergy :
      Four.section4AggregateConstant * (gradient * energy)
      ≤ (Four.section4AggregateConstant * smallness) * energy
    toCoefficientTimesEnergy =
      subst
        (λ upper →
          Four.section4AggregateConstant * (gradient * energy)
          ≤ upper)
        reassociateUpper
        scaledGradientEnergyBelow

    coefficientTimesEnergyBelow :
      (Four.section4AggregateConstant * smallness) * energy
      ≤ absorptionCoefficient * energy
    coefficientTimesEnergyBelow =
      let
        instance
          energyIsNonnegative = nonNegative energyNonnegative
      in
      ℚₚ.*-monoʳ-≤-nonNeg energy coefficientSmall
  in
  ℚₚ.≤-trans
    toCoefficientTimesEnergy
    coefficientTimesEnergyBelow

record FiniteSection4AbsorptionData : Set where
  constructor finite-section4-absorption
  field
    interactions : Four.FiniteFourInteractionData
    lowCutoff gapCutoff : Nat

    smallness absorptionCoefficient : ℚ

    lowGradientBelowSmallness :
      Four.lowGradient interactions ≤ smallness

    aggregateSmallnessBelowAbsorption :
      Four.section4AggregateConstant * smallness
      ≤ absorptionCoefficient

open FiniteSection4AbsorptionData public

finiteSection4TotalAbsorbed :
  (data : FiniteSection4AbsorptionData) →
  Four.section4TotalMagnitude
    (interactions data)
    (lowCutoff data)
    (gapCutoff data)
  ≤ absorptionCoefficient data
      * Four.weightedEnergy (interactions data)
finiteSection4TotalAbsorbed data =
  ℚₚ.≤-trans
    (Four.section4TotalFiniteBound
      (interactions data)
      (lowCutoff data)
      (gapCutoff data))
    (smallGradientAbsorption
      (Four.lowGradient (interactions data))
      (Four.weightedEnergy (interactions data))
      (smallness data)
      (absorptionCoefficient data)
      (Four.weightedEnergyNonnegative (interactions data))
      (lowGradientBelowSmallness data)
      (aggregateSmallnessBelowAbsorption data))

finiteSmallGradientAbsorptionClosed : Bool
finiteSmallGradientAbsorptionClosed = true

exactSection4ConstantUsedInAbsorption : Bool
exactSection4ConstantUsedInAbsorption = true

finiteSmallGradientAbsorptionClosedIsTrue :
  finiteSmallGradientAbsorptionClosed ≡ true
finiteSmallGradientAbsorptionClosedIsTrue = refl

exactSection4ConstantUsedInAbsorptionIsTrue :
  exactSection4ConstantUsedInAbsorption ≡ true
exactSection4ConstantUsedInAbsorptionIsTrue = refl
