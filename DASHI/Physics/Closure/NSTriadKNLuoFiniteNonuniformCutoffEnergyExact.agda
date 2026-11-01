module DASHI.Physics.Closure.NSTriadKNLuoFiniteNonuniformCutoffEnergyExact where

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
-- Mathematical ingredient: nonuniform finite summation by parts.
-- DOI: not applicable to this repository-specialised finite identity.
--
-- PURPOSE
-- Prove the finite nonuniform-time version of the cutoff-energy calculation.
-- A step of length h_n carries the source-faithful inequality
--
--   E_{n+1}-E_n + h_n D_n <= h_n Pi_n.
--
-- Multiplication by a nonnegative cutoff eta_n and exact summation by parts
-- give
--
--   eta_N E_{N+1} - eta_0 E_0 - cutoffError
--     + sum_n eta_n h_n D_n
--       <= sum_n eta_n h_n Pi_n.
--
-- The theorem is derived by instantiating the existing exact product-rule
-- proof with the step-scaled dissipation and flux; no continuum integral or
-- final cutoff estimate is assumed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; _-_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ

import DASHI.Physics.Closure.NSTriadKNOutputRelocationPositiveKernelMajorant as Sum
import DASHI.Physics.Closure.NSTriadKNLuoDiscreteCutoffEnergyExact as Cutoff

record NonuniformCutoffEnergyData : Set₁ where
  field
    energy dissipation flux cutoff stepLength : Nat → ℚ
    lastStep : Nat

    cutoffNonnegative :
      (step : Nat) → 0ℚ ≤ cutoff step

    stepLengthNonnegative :
      (step : Nat) → 0ℚ ≤ stepLength step

    nonuniformStepEnergyInequality :
      (step : Nat) →
      Cutoff.energyIncrement energy step
        + stepLength step * dissipation step
      ≤ stepLength step * flux step

open NonuniformCutoffEnergyData public

asUniformlyIndexedCutoffData :
  NonuniformCutoffEnergyData → Cutoff.DiscreteCutoffEnergyData
asUniformlyIndexedCutoffData data = record
  { energy = energy data
  ; dissipation = λ step →
      stepLength data step * dissipation data step
  ; flux = λ step →
      stepLength data step * flux data step
  ; cutoff = cutoff data
  ; lastStep = lastStep data
  ; cutoffNonnegative = cutoffNonnegative data
  ; stepEnergyInequality = nonuniformStepEnergyInequality data
  }

nonuniformWeightedDissipation :
  NonuniformCutoffEnergyData → ℚ
nonuniformWeightedDissipation data =
  Sum.sumTo
    (λ step →
      cutoff data step
      * (stepLength data step * dissipation data step))
    (lastStep data)

nonuniformWeightedFlux :
  NonuniformCutoffEnergyData → ℚ
nonuniformWeightedFlux data =
  Sum.sumTo
    (λ step →
      cutoff data step
      * (stepLength data step * flux data step))
    (lastStep data)

nonuniformDissipationMatchesCutoffAdapter :
  (data : NonuniformCutoffEnergyData) →
  Cutoff.weightedDissipation (asUniformlyIndexedCutoffData data)
  ≡ nonuniformWeightedDissipation data
nonuniformDissipationMatchesCutoffAdapter data = refl

nonuniformFluxMatchesCutoffAdapter :
  (data : NonuniformCutoffEnergyData) →
  Cutoff.weightedFlux (asUniformlyIndexedCutoffData data)
  ≡ nonuniformWeightedFlux data
nonuniformFluxMatchesCutoffAdapter data = refl

finiteNonuniformIntegratedCutoffEnergy :
  (data : NonuniformCutoffEnergyData) →
  cutoff data (lastStep data)
      * energy data (suc (lastStep data))
    - cutoff data zero * energy data zero
    - Cutoff.cutoffDifferenceError
        (cutoff data) (energy data) (lastStep data)
    + nonuniformWeightedDissipation data
  ≤ nonuniformWeightedFlux data
finiteNonuniformIntegratedCutoffEnergy data =
  Cutoff.discreteIntegratedCutoffEnergyInequality
    (asUniformlyIndexedCutoffData data)

scaledDissipationNonnegative :
  (data : NonuniformCutoffEnergyData) →
  ((step : Nat) → 0ℚ ≤ dissipation data step) →
  (step : Nat) →
  0ℚ ≤ stepLength data step * dissipation data step
scaledDissipationNonnegative data dissipationNonnegative step =
  let
    instance
      hIsNonnegative = nonNegative (stepLengthNonnegative data step)
      dIsNonnegative = nonNegative (dissipationNonnegative step)
      productIsNonnegative =
        ℚₚ.nonNeg*nonNeg⇒nonNeg
          (stepLength data step)
          (dissipation data step)
  in
  ℚₚ.nonNegative⁻¹
    (stepLength data step * dissipation data step)

finiteNonuniformCutoffEnergyClosed : Bool
finiteNonuniformCutoffEnergyClosed = true

finiteNonuniformCutoffEnergyClosedIsTrue :
  finiteNonuniformCutoffEnergyClosed ≡ true
finiteNonuniformCutoffEnergyClosedIsTrue = refl
