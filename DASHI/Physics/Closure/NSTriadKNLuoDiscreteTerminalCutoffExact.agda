module DASHI.Physics.Closure.NSTriadKNLuoDiscreteTerminalCutoffExact where

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
-- Give a fully concrete finite terminal cutoff and discharge its support,
-- endpoint, nonnegativity and derivative-error algebra.  The cutoff is the
-- discrete Heaviside profile
--
--   eta_0 = 0,  eta_n = 1 for n >= 1.
--
-- Its forward difference is supported only at the first step, so the complete
-- cutoff-derivative error is exactly E_1.  Combining this with the finite
-- cutoff-energy theorem produces a concrete terminal inequality with no
-- abstract cutoff fields.
--
-- This is a finite-time model of the source cutoff, not a claim that the
-- continuum smooth cutoff or its derivative bounds have already been built.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _-_; _≤_)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo
import DASHI.Physics.Closure.NSTriadKNLuoDiscreteCutoffEnergyExact as CutoffEnergy

terminalCutoff : Nat → ℚ
terminalCutoff zero = 0ℚ
terminalCutoff (suc step) = 1ℚ

terminalCutoffVanishesAtStart : terminalCutoff zero ≡ 0ℚ
terminalCutoffVanishesAtStart = refl

terminalCutoffEqualsOneAfterStart :
  (step : Nat) → terminalCutoff (suc step) ≡ 1ℚ
terminalCutoffEqualsOneAfterStart step = refl

terminalCutoffNonnegative :
  (step : Nat) → 0ℚ ≤ terminalCutoff step
terminalCutoffNonnegative zero = ℚₚ.≤-refl
terminalCutoffNonnegative (suc step) = Geo.zeroBelowOne

terminalCutoffForwardDifference : Nat → ℚ
terminalCutoffForwardDifference step =
  terminalCutoff (suc step) - terminalCutoff step

terminalCutoffDifferenceAtStart :
  terminalCutoffForwardDifference zero ≡ 1ℚ
terminalCutoffDifferenceAtStart = refl

terminalCutoffDifferenceAfterStart :
  (step : Nat) →
  terminalCutoffForwardDifference (suc step) ≡ 0ℚ
terminalCutoffDifferenceAfterStart step =
  solve []

terminalCutoffDifferenceError :
  (energy : Nat → ℚ) →
  (step : Nat) →
  CutoffEnergy.cutoffDifferenceError terminalCutoff energy (suc step)
  ≡ energy (suc zero)
terminalCutoffDifferenceError energy zero =
  solve (energy (suc zero) ∷ [])
terminalCutoffDifferenceError energy (suc step)
  rewrite terminalCutoffDifferenceAfterStart step
        | terminalCutoffDifferenceError energy step =
  solve (energy (suc zero) ∷ energy (suc (suc step)) ∷ [])

record ConcreteTerminalCutoffEnergyData : Set₁ where
  field
    energy dissipation flux : Nat → ℚ
    lastInteriorStep : Nat

    stepEnergyInequality :
      (step : Nat) →
      CutoffEnergy.energyIncrement energy step + dissipation step
      ≤ flux step

open ConcreteTerminalCutoffEnergyData public

concreteCutoffEnergyData :
  ConcreteTerminalCutoffEnergyData →
  CutoffEnergy.DiscreteCutoffEnergyData
concreteCutoffEnergyData data = record
  { energy = energy data
  ; dissipation = dissipation data
  ; flux = flux data
  ; cutoff = terminalCutoff
  ; lastStep = suc (lastInteriorStep data)
  ; cutoffNonnegative = terminalCutoffNonnegative
  ; stepEnergyInequality = stepEnergyInequality data
  }

concreteWeightedDissipation :
  ConcreteTerminalCutoffEnergyData → ℚ
concreteWeightedDissipation data =
  CutoffEnergy.weightedDissipation (concreteCutoffEnergyData data)

concreteWeightedFlux :
  ConcreteTerminalCutoffEnergyData → ℚ
concreteWeightedFlux data =
  CutoffEnergy.weightedFlux (concreteCutoffEnergyData data)

terminalCutoffBoundaryExpression :
  (data : ConcreteTerminalCutoffEnergyData) →
  terminalCutoff (suc (lastInteriorStep data))
      * energy data (suc (suc (lastInteriorStep data)))
    - terminalCutoff zero * energy data zero
    - CutoffEnergy.cutoffDifferenceError
        terminalCutoff
        (energy data)
        (suc (lastInteriorStep data))
    + concreteWeightedDissipation data
  ≡ energy data (suc (suc (lastInteriorStep data)))
    - energy data (suc zero)
    + concreteWeightedDissipation data
terminalCutoffBoundaryExpression data
  rewrite terminalCutoffDifferenceError
    (energy data) (lastInteriorStep data) =
  solve
    ( energy data (suc (suc (lastInteriorStep data)))
    ∷ energy data (suc zero)
    ∷ concreteWeightedDissipation data
    ∷ energy data zero
    ∷ []
    )

concreteTerminalCutoffEnergyInequality :
  (data : ConcreteTerminalCutoffEnergyData) →
  energy data (suc (suc (lastInteriorStep data)))
    - energy data (suc zero)
    + concreteWeightedDissipation data
  ≤ concreteWeightedFlux data
concreteTerminalCutoffEnergyInequality data =
  subst
    (λ left → left ≤ concreteWeightedFlux data)
    (terminalCutoffBoundaryExpression data)
    (CutoffEnergy.discreteIntegratedCutoffEnergyInequality
      (concreteCutoffEnergyData data))

concreteDiscreteTerminalCutoffClosed : Bool
concreteDiscreteTerminalCutoffClosed = true

concreteTerminalCutoffEnergyInequalityClosed : Bool
concreteTerminalCutoffEnergyInequalityClosed = true

concreteDiscreteTerminalCutoffClosedIsTrue :
  concreteDiscreteTerminalCutoffClosed ≡ true
concreteDiscreteTerminalCutoffClosedIsTrue = refl

concreteTerminalCutoffEnergyInequalityClosedIsTrue :
  concreteTerminalCutoffEnergyInequalityClosed ≡ true
concreteTerminalCutoffEnergyInequalityClosedIsTrue = refl
