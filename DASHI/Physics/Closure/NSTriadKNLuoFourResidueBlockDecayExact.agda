module DASHI.Physics.Closure.NSTriadKNLuoFourResidueBlockDecayExact where

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
-- PURPOSE
-- Carry the explicit b=4 weighted-criterion contraction through all four
-- residue classes.  A proof-relevant path stores only
--
--   A_{r+4(k+1)} <= (1/4) A_{r+4k}.
--
-- Induction derives A_{r+4k} <= (1/4)^k A_r.  Since 1/4 is exactly
-- 2^{4(1-3/2)}, this is the four-aligned lambda^{1-alpha} decay needed for
-- Luo's terminal criterion.  The terminal decay theorem is not an input.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNLuoAlphaThreeHalvesConstantsExact as Alpha
import DASHI.Physics.Closure.NSTriadKNLuoAlphaThreeHalvesFourShiftBootstrapExact as Bootstrap
import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo

quarter : ℚ
quarter = Geo.quarter

quarterNonnegative : 0ℚ ≤ quarter
quarterNonnegative = Geo.quarterNonnegative

quarterPower : Nat → ℚ
quarterPower zero = 1ℚ
quarterPower (suc n) = quarter * quarterPower n

data QuarterContractionPath : ℚ → Nat → ℚ → Set where
  start : (quantity : ℚ) → QuarterContractionPath quantity zero quantity

  contract :
    ∀ {initial steps current next} →
    QuarterContractionPath initial steps current →
    next ≤ quarter * current →
    QuarterContractionPath initial (suc steps) next

quarterContractionPathBound :
  ∀ {initial steps terminal} →
  QuarterContractionPath initial steps terminal →
  terminal ≤ quarterPower steps * initial
quarterContractionPathBound {initial = initial} (start .initial) =
  let identity : quarterPower zero * initial ≡ initial
      identity = solve (initial ∷ [])
  in
  subst (λ right → initial ≤ right) (sym identity) ℚₚ.≤-refl
quarterContractionPathBound
  {initial = initial} {steps = suc steps} {terminal = next}
  (contract {current = current} path nextBound) =
  let
    induction : current ≤ quarterPower steps * initial
    induction = quarterContractionPathBound path

    scaled :
      quarter * current ≤ quarter * (quarterPower steps * initial)
    scaled =
      let instance quarterIsNonnegative = nonNegative quarterNonnegative
      in ℚₚ.*-monoˡ-≤-nonNeg quarter induction

    reassociate :
      quarter * (quarterPower steps * initial)
      ≡ quarterPower (suc steps) * initial
    reassociate = solve (quarter ∷ quarterPower steps ∷ initial ∷ [])
  in
  ℚₚ.≤-trans nextBound
    (subst (λ right → quarter * current ≤ right) reassociate scaled)

alignedShell : Nat → Nat → Nat
alignedShell residue block = residue + Alpha.fourTimes block

record FourResidueBlockDecayData : Set₁ where
  field
    weightedCriterionAt : Nat → ℚ
    baseCriterion : Nat → ℚ

    baseMeaning :
      (residue : Nat) →
      weightedCriterionAt (alignedShell residue zero)
      ≡ baseCriterion residue

    pathAt :
      (residue block : Nat) →
      QuarterContractionPath
        (baseCriterion residue)
        block
        (weightedCriterionAt (alignedShell residue block))

open FourResidueBlockDecayData public

alignedBlockDecay :
  (data : FourResidueBlockDecayData) →
  (residue block : Nat) →
  weightedCriterionAt data (alignedShell residue block)
  ≤ quarterPower block * baseCriterion data residue
alignedBlockDecay data residue block =
  quarterContractionPathBound (pathAt data residue block)

zeroResidueDecay :
  (data : FourResidueBlockDecayData) →
  (block : Nat) →
  weightedCriterionAt data (alignedShell zero block)
  ≤ quarterPower block * baseCriterion data zero
zeroResidueDecay data = alignedBlockDecay data zero

oneResidueDecay :
  (data : FourResidueBlockDecayData) →
  (block : Nat) →
  weightedCriterionAt data (alignedShell (suc zero) block)
  ≤ quarterPower block * baseCriterion data (suc zero)
oneResidueDecay data = alignedBlockDecay data (suc zero)

twoResidueDecay :
  (data : FourResidueBlockDecayData) →
  (block : Nat) →
  weightedCriterionAt data (alignedShell (suc (suc zero)) block)
  ≤ quarterPower block * baseCriterion data (suc (suc zero))
twoResidueDecay data = alignedBlockDecay data (suc (suc zero))

threeResidueDecay :
  (data : FourResidueBlockDecayData) →
  (block : Nat) →
  weightedCriterionAt data (alignedShell (suc (suc (suc zero))) block)
  ≤ quarterPower block * baseCriterion data (suc (suc (suc zero)))
threeResidueDecay data = alignedBlockDecay data (suc (suc (suc zero)))

explicitBootstrapCoefficientFitsQuarter :
  Bootstrap.combinedCoefficient ≤ quarter
explicitBootstrapCoefficientFitsQuarter =
  Bootstrap.combinedCoefficientBelowQuarter
