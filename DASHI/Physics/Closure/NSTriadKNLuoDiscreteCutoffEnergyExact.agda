module DASHI.Physics.Closure.NSTriadKNLuoDiscreteCutoffEnergyExact where

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
-- Mathematical ingredient: finite summation by parts (the discrete product
-- rule / Abel transformation).  This classical finite identity has no single
-- source DOI; the repository proof below is by exact rational induction.
--
-- PURPOSE
-- Prove the finite-time analogue of the cutoff-energy calculation rather than
-- treating integration by parts as an opaque leaf.  For rational sequences
-- eta_n and E_n,
--
--   sum_{n=0}^N eta_n (E_{n+1}-E_n)
--
-- is exactly the terminal boundary term minus the initial term and the
-- discrete cutoff-derivative error.  Combining this identity with a pointwise
-- energy inequality and eta_n >= 0 gives the complete finite integrated
-- cutoff-energy inequality.
--
-- The remaining continuum seam is passage from these finite sums and
-- differences to the absolutely-continuous time integral and a.e. derivative.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; _-_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

import DASHI.Physics.Closure.NSTriadKNOutputRelocationPositiveKernelMajorant as Sum

energyIncrement : (Nat → ℚ) → Nat → ℚ
energyIncrement energy step = energy (suc step) - energy step

weightedDerivativeSum :
  (Nat → ℚ) →
  (Nat → ℚ) →
  Nat →
  ℚ
weightedDerivativeSum cutoff energy lastStep =
  Sum.sumTo
    (λ step → cutoff step * energyIncrement energy step)
    lastStep

cutoffDifferenceError :
  (Nat → ℚ) →
  (Nat → ℚ) →
  Nat →
  ℚ
cutoffDifferenceError cutoff energy zero = 0ℚ
cutoffDifferenceError cutoff energy (suc step) =
  (cutoff (suc step) - cutoff step) * energy (suc step)
  + cutoffDifferenceError cutoff energy step

discreteProductRule :
  ∀ cutoffNow cutoffNext energyNow energyNext →
  cutoffNext * energyNext - cutoffNow * energyNow
  ≡ cutoffNow * (energyNext - energyNow)
    + (cutoffNext - cutoffNow) * energyNext
discreteProductRule cutoffNow cutoffNext energyNow energyNext =
  solve (cutoffNow ∷ cutoffNext ∷ energyNow ∷ energyNext ∷ [])

discreteSummationByParts :
  (cutoff energy : Nat → ℚ) →
  (lastStep : Nat) →
  weightedDerivativeSum cutoff energy lastStep
  ≡ cutoff lastStep * energy (suc lastStep)
    - cutoff zero * energy zero
    - cutoffDifferenceError cutoff energy lastStep
discreteSummationByParts cutoff energy zero =
  solve (cutoff zero ∷ energy zero ∷ energy (suc zero) ∷ [])
discreteSummationByParts cutoff energy (suc step)
  rewrite discreteSummationByParts cutoff energy step =
  solve
    ( cutoff (suc step)
    ∷ cutoff step
    ∷ cutoff zero
    ∷ energy (suc (suc step))
    ∷ energy (suc step)
    ∷ energy zero
    ∷ cutoffDifferenceError cutoff energy step
    ∷ []
    )

sumWeightedAdditiveSplit :
  (weight left right : Nat → ℚ) →
  (lastStep : Nat) →
  Sum.sumTo
    (λ step → weight step * (left step + right step))
    lastStep
  ≡ Sum.sumTo (λ step → weight step * left step) lastStep
    + Sum.sumTo (λ step → weight step * right step) lastStep
sumWeightedAdditiveSplit weight left right zero =
  solve (weight zero ∷ left zero ∷ right zero ∷ [])
sumWeightedAdditiveSplit weight left right (suc step)
  rewrite sumWeightedAdditiveSplit weight left right step =
  solve
    ( weight (suc step)
    ∷ left (suc step)
    ∷ right (suc step)
    ∷ Sum.sumTo (λ index → weight index * left index) step
    ∷ Sum.sumTo (λ index → weight index * right index) step
    ∷ []
    )

record DiscreteCutoffEnergyData : Set₁ where
  field
    energy dissipation flux cutoff : Nat → ℚ
    lastStep : Nat

    cutoffNonnegative :
      (step : Nat) → 0ℚ ≤ cutoff step

    stepEnergyInequality :
      (step : Nat) →
      energyIncrement energy step + dissipation step
      ≤ flux step

open DiscreteCutoffEnergyData public

weightedStepEnergyInequality :
  (data : DiscreteCutoffEnergyData) →
  (step : Nat) →
  cutoff data step
    * (energyIncrement (energy data) step + dissipation data step)
  ≤ cutoff data step * flux data step
weightedStepEnergyInequality data step =
  let
    instance cutoffNN =
      nonNegative (cutoffNonnegative data step)
  in
  ℚₚ.*-monoˡ-≤-nonNeg
    (cutoff data step)
    (stepEnergyInequality data step)

summedWeightedEnergyInequality :
  (data : DiscreteCutoffEnergyData) →
  Sum.sumTo
    (λ step →
      cutoff data step
      * (energyIncrement (energy data) step + dissipation data step))
    (lastStep data)
  ≤ Sum.sumTo
      (λ step → cutoff data step * flux data step)
      (lastStep data)
summedWeightedEnergyInequality data =
  Sum.sumToMonotone
    (λ step →
      cutoff data step
      * (energyIncrement (energy data) step + dissipation data step))
    (λ step → cutoff data step * flux data step)
    (lastStep data)
    (weightedStepEnergyInequality data)

weightedDissipation : DiscreteCutoffEnergyData → ℚ
weightedDissipation data =
  Sum.sumTo
    (λ step → cutoff data step * dissipation data step)
    (lastStep data)

weightedFlux : DiscreteCutoffEnergyData → ℚ
weightedFlux data =
  Sum.sumTo
    (λ step → cutoff data step * flux data step)
    (lastStep data)

weightedEnergySplit :
  (data : DiscreteCutoffEnergyData) →
  Sum.sumTo
    (λ step →
      cutoff data step
      * (energyIncrement (energy data) step + dissipation data step))
    (lastStep data)
  ≡ weightedDerivativeSum
      (cutoff data) (energy data) (lastStep data)
    + weightedDissipation data
weightedEnergySplit data =
  sumWeightedAdditiveSplit
    (cutoff data)
    (energyIncrement (energy data))
    (dissipation data)
    (lastStep data)

weightedEnergyBoundaryIdentity :
  (data : DiscreteCutoffEnergyData) →
  Sum.sumTo
    (λ step →
      cutoff data step
      * (energyIncrement (energy data) step + dissipation data step))
    (lastStep data)
  ≡ cutoff data (lastStep data)
      * energy data (suc (lastStep data))
    - cutoff data zero * energy data zero
    - cutoffDifferenceError
        (cutoff data) (energy data) (lastStep data)
    + weightedDissipation data
weightedEnergyBoundaryIdentity data =
  trans
    (weightedEnergySplit data)
    (cong
      (λ derivative → derivative + weightedDissipation data)
      (discreteSummationByParts
        (cutoff data)
        (energy data)
        (lastStep data)))

discreteIntegratedCutoffEnergyInequality :
  (data : DiscreteCutoffEnergyData) →
  cutoff data (lastStep data)
      * energy data (suc (lastStep data))
    - cutoff data zero * energy data zero
    - cutoffDifferenceError
        (cutoff data) (energy data) (lastStep data)
    + weightedDissipation data
  ≤ weightedFlux data
discreteIntegratedCutoffEnergyInequality data =
  subst
    (λ left → left ≤ weightedFlux data)
    (weightedEnergyBoundaryIdentity data)
    (summedWeightedEnergyInequality data)

discreteCutoffProductRuleClosed : Bool
discreteCutoffProductRuleClosed = true

discreteSummationByPartsClosed : Bool
discreteSummationByPartsClosed = true

discreteIntegratedCutoffEnergyClosed : Bool
discreteIntegratedCutoffEnergyClosed = true

discreteCutoffProductRuleClosedIsTrue :
  discreteCutoffProductRuleClosed ≡ true
discreteCutoffProductRuleClosedIsTrue = refl

discreteSummationByPartsClosedIsTrue :
  discreteSummationByPartsClosed ≡ true
discreteSummationByPartsClosedIsTrue = refl

discreteIntegratedCutoffEnergyClosedIsTrue :
  discreteIntegratedCutoffEnergyClosed ≡ true
discreteIntegratedCutoffEnergyClosedIsTrue = refl
