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
-- residue classes.  The input family supplies one concrete Section-4
-- recursion datum per residue and block together with equalities identifying
-- its predecessor and output with the physical weighted criterion.  From
-- those local data this module constructs the proof-relevant path
--
--   A_{r+4(k+1)} <= (1/4) A_{r+4k}
--
-- and induction derives A_{r+4k} <= (1/4)^k A_r.  The path and terminal
-- decay theorem are therefore not fields of the input package.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
import Data.Nat.Base as Nat
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using
  (cong; subst; subst₂; sym; trans)

import DASHI.Physics.Closure.NSTriadKNLuoAlphaThreeHalvesConstantsExact as Alpha
import DASHI.Physics.Closure.NSTriadKNLuoAlphaThreeHalvesFourShiftBootstrapExact as Bootstrap
import DASHI.Physics.Closure.NSTriadKNLuoFiniteCutoffSection4RecursionExact as Cutoff
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
  let
    identity : quarterPower zero * initial ≡ initial
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
      let
        instance
          quarterIsNonnegative = nonNegative quarterNonnegative
      in
      ℚₚ.*-monoˡ-≤-nonNeg quarter induction

    reassociate :
      quarter * (quarterPower steps * initial)
      ≡ quarterPower (suc steps) * initial
    reassociate = solve (quarter ∷ quarterPower steps ∷ initial ∷ [])
  in
  ℚₚ.≤-trans nextBound
    (subst (λ right → quarter * current ≤ right) reassociate scaled)

alignedShell : Nat → Nat → Nat
alignedShell residue block =
  Nat._+_ residue (Alpha.fourTimes block)

recursionOutput :
  Bootstrap.ExplicitFourShiftRecursionData → ℚ
recursionOutput recursionData =
  Cutoff.outputEnergy
      (Bootstrap.cutoffData (Bootstrap.absorptionData recursionData))
    + Cutoff.dissipation
        (Bootstrap.cutoffData (Bootstrap.absorptionData recursionData))

record FourResidueBlockRecursionFamily : Set₁ where
  field
    weightedCriterionAt : Nat → ℚ
    baseCriterion : Nat → ℚ

    baseMeaning :
      (residue : Nat) →
      weightedCriterionAt (alignedShell residue zero)
      ≡ baseCriterion residue

    recursionAt :
      (residue block : Nat) →
      Bootstrap.ExplicitFourShiftRecursionData

    predecessorMeaning :
      (residue block : Nat) →
      Bootstrap.predecessorMajorant (recursionAt residue block)
      ≡ weightedCriterionAt (alignedShell residue block)

    outputMeaning :
      (residue block : Nat) →
      recursionOutput (recursionAt residue block)
      ≡ weightedCriterionAt (alignedShell residue (suc block))

open FourResidueBlockRecursionFamily public

targetCoefficientIsQuarter : Bootstrap.targetCoefficient ≡ quarter
targetCoefficientIsQuarter = refl

oneBlockQuarterContraction :
  (family : FourResidueBlockRecursionFamily) →
  (residue block : Nat) →
  weightedCriterionAt family (alignedShell residue (suc block))
  ≤ quarter * weightedCriterionAt family (alignedShell residue block)
oneBlockQuarterContraction family residue block =
  let
    recurrence = recursionAt family residue block

    raw :
      recursionOutput recurrence
      ≤ Bootstrap.targetCoefficient
          * Bootstrap.predecessorMajorant recurrence
    raw = Bootstrap.explicitFourShiftContraction recurrence

    rightMeaning :
      Bootstrap.targetCoefficient
        * Bootstrap.predecessorMajorant recurrence
      ≡ quarter
          * weightedCriterionAt family (alignedShell residue block)
    rightMeaning =
      trans
        (cong
          (λ coefficient →
            coefficient * Bootstrap.predecessorMajorant recurrence)
          targetCoefficientIsQuarter)
        (cong
          (quarter *_)
          (predecessorMeaning family residue block))
  in
  subst₂ _≤_
    (outputMeaning family residue block)
    rightMeaning
    raw

constructedQuarterPath :
  (family : FourResidueBlockRecursionFamily) →
  (residue block : Nat) →
  QuarterContractionPath
    (baseCriterion family residue)
    block
    (weightedCriterionAt family (alignedShell residue block))
constructedQuarterPath family residue zero =
  subst
    (λ terminal →
      QuarterContractionPath
        (baseCriterion family residue) zero terminal)
    (sym (baseMeaning family residue))
    (start (baseCriterion family residue))
constructedQuarterPath family residue (suc block) =
  contract
    (constructedQuarterPath family residue block)
    (oneBlockQuarterContraction family residue block)

alignedBlockDecay :
  (family : FourResidueBlockRecursionFamily) →
  (residue block : Nat) →
  weightedCriterionAt family (alignedShell residue block)
  ≤ quarterPower block * baseCriterion family residue
alignedBlockDecay family residue block =
  quarterContractionPathBound
    (constructedQuarterPath family residue block)

zeroResidueDecay :
  (family : FourResidueBlockRecursionFamily) →
  (block : Nat) →
  weightedCriterionAt family (alignedShell zero block)
  ≤ quarterPower block * baseCriterion family zero
zeroResidueDecay family = alignedBlockDecay family zero

oneResidueDecay :
  (family : FourResidueBlockRecursionFamily) →
  (block : Nat) →
  weightedCriterionAt family (alignedShell (suc zero) block)
  ≤ quarterPower block * baseCriterion family (suc zero)
oneResidueDecay family = alignedBlockDecay family (suc zero)

twoResidueDecay :
  (family : FourResidueBlockRecursionFamily) →
  (block : Nat) →
  weightedCriterionAt family (alignedShell (suc (suc zero)) block)
  ≤ quarterPower block * baseCriterion family (suc (suc zero))
twoResidueDecay family = alignedBlockDecay family (suc (suc zero))

threeResidueDecay :
  (family : FourResidueBlockRecursionFamily) →
  (block : Nat) →
  weightedCriterionAt family (alignedShell (suc (suc (suc zero))) block)
  ≤ quarterPower block * baseCriterion family (suc (suc (suc zero)))
threeResidueDecay family = alignedBlockDecay family (suc (suc (suc zero)))

explicitBootstrapCoefficientFitsQuarter :
  Bootstrap.combinedCoefficient ≤ quarter
explicitBootstrapCoefficientFitsQuarter =
  Bootstrap.combinedCoefficientBelowQuarter
