module DASHI.Chemistry.HydrogenFuelCycleBreakEvenExact where

-- Attribution:
-- Natural-number order and additive cancellation: standard constructive
-- arithmetic, using DASHI.Core.Prelude / Agda standard-library provenance.
-- This concrete hydrogen/fuel audit was directed by the user and drafted by
-- ChatGPT on 2026-11-09. No original combustion, electrolysis, or physical
-- efficiency law is attributed to either party.
--
-- This is a purely algebraic, matched-output, same-unit input comparison.
-- Diesel fuel and external electricity both count as energy inputs.
-- It is NOT a measured engine-efficiency improvement.

open import DASHI.Core.Prelude
  using (Nat; zero; suc; _+_; _<_; _≡_; refl; sym; subst; s≤s)

record Equivalence (P Q : Set) : Set where
  field
    forward : P → Q
    backward : Q → P

open Equivalence public

-- Exact cancellation of a fixed fuel input under strict comparison.
-- A proof of a < b is equivalent to a proof of n + a < n + b.
addLeftStrict :
  (n a b : Nat) → a < b → n + a < n + b
addLeftStrict zero a b p = p
addLeftStrict (suc n) a b p =
  s≤s (addLeftStrict n a b p)

removeLeftStrict :
  (n a b : Nat) → n + a < n + b → a < b
removeLeftStrict zero a b p = p
removeLeftStrict (suc n) a b (s≤s p) =
  removeLeftStrict n a b p

record FossilDisplacement : Set where
  field
    baselineFuel : Nat
    assistedFuel : Nat
    displacedFuel : Nat
    externalElectricity : Nat
    exactDisplacement :
      baselineFuel ≡ assistedFuel + displacedFuel

open FossilDisplacement public

-- Total-input savings is exactly the condition that externally supplied
-- electricity is smaller than the original diesel energy displaced.
-- This does not depend on any assumed engine efficiency or catalyst claim.
energySavingIffDisplacementExceedsElectricity :
  (s : FossilDisplacement) →
  Equivalence
    (assistedFuel s + externalElectricity s < baselineFuel s)
    (externalElectricity s < displacedFuel s)
energySavingIffDisplacementExceedsElectricity s = record
  { forward = λ p →
      removeLeftStrict
        (assistedFuel s)
        (externalElectricity s)
        (displacedFuel s)
        (subst
          (λ bound → assistedFuel s + externalElectricity s < bound)
          (exactDisplacement s)
          p)
  ; backward = λ p →
      subst
        (λ bound → assistedFuel s + externalElectricity s < bound)
        (sym (exactDisplacement s))
        (addLeftStrict
          (assistedFuel s)
          (externalElectricity s)
          (displacedFuel s)
          p)
  }

-- Under exactly equal engine efficiency and useful output, the maximal
-- displaced diesel chemical energy is at most the injected combustible
-- H2/synthetic-fuel energy. Whether H2 changes the efficiency is a separate
-- empirical question, NOT inferred here.
record SameEfficiencySubstitution : Set where
  field
    fossil : FossilDisplacement
    externallyProducedCombustibleEnergy : Nat
    displacementUpperBound :
      displacedFuel fossil < suc externallyProducedCombustibleEnergy

open SameEfficiencySubstitution public

-- A unit-energy numerical regression: 15 input, 10 replacement, 100 baseline,
-- 90 assisted. This cannot be a strict total-input saving.
tenFromFifteen : FossilDisplacement
tenFromFifteen = record
  { baselineFuel = 100
  ; assistedFuel = 90
  ; displacedFuel = 10
  ; externalElectricity = 15
  ; exactDisplacement = refl }

tenFromFifteenDoesNotSaveEnergy :
  (assistedFuel tenFromFifteen + externalElectricity tenFromFifteen
     < baselineFuel tenFromFifteen) →
  externalElectricity tenFromFifteen < displacedFuel tenFromFifteen
tenFromFifteenDoesNotSaveEnergy =
  forward (energySavingIffDisplacementExceedsElectricity tenFromFifteen)

-- The certificate above is a one-way consequence of any supposed saving;
-- it deliberately does not manufacture such a saving or a measured η gain.
