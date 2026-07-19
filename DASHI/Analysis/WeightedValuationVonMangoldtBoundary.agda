module DASHI.Analysis.WeightedValuationVonMangoldtBoundary where

-- The existing weighted-valuation carrier is useful prime-indexed arithmetic,
-- but it is not the classical von Mangoldt weight.  Valuation energy multiplies
-- by p-adic depth; Λ(p^k) keeps the same log p weight for every k ≥ 1.
-- This module makes the correction obligation explicit.

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Nat using (_*_)
open import DASHI.TrackedPrimes using (SSP; toNat)
open import DASHI.Arithmetic.ArithmeticIntegerEmbedding using (Int)
open import DASHI.Arithmetic.WeightedValuationEnergy using
  ( valuationAt
  ; weight
  ; weightedValuationAt
  ; weightedValuationEnergySurface
  )
open import DASHI.Analysis.WeilTestSpace
open import DASHI.Analysis.RiemannPrimePowerArithmetic

_≢_ : {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

-- Nat-valued stand-in used only to expose the multiplicity mismatch.  The real
-- explicit formula needs log p in an analytic scalar carrier, not this proxy.
trackedMangoldtNatProxy : SSP → Nat
trackedMangoldtNatProxy p = toNat p

multiplicityTwoChangesValuationWeight :
  (p : SSP) →
  (n : Int) →
  valuationAt p n ≡ 2 →
  (weight p * 2) ≢ weight p →
  weightedValuationAt p n ≢ trackedMangoldtNatProxy p
multiplicityTwoChangesValuationWeight p n depth twoWeightsDiffer
  rewrite depth = twoWeightsDiffer

record WeightedValuationToVonMangoldtBridge
  (space : WeilTestSpace) : Set₁ where
  open WeilTestSpace space
  field
    primePowerKernel : PrimePowerKernel space

    embedInteger : Int → Test
    natWeightToScalar : Nat → Scalar

    -- Extends the finite tracked support to every prime required by the Euler
    -- product / explicit formula.
    AllPrimeSupport : Set
    allPrimeSupport : AllPrimeSupport

    -- Replaces the Nat proxy p with the actual logarithmic scalar log p.
    LogarithmicWeightCompatibility : Set
    logarithmicWeightCompatibility : LogarithmicWeightCompatibility

    -- Removes valuation multiplicity: p·v_p(n) is not Λ(n).
    MultiplicityCollapseCompatibility : Set
    multiplicityCollapseCompatibility :
      MultiplicityCollapseCompatibility

    -- Connects the corrected arithmetic carrier to prime-power test samples.
    PrimePowerSamplingCompatibility : Set
    primePowerSamplingCompatibility :
      PrimePowerSamplingCompatibility

record CurrentWeightedValuationZetaBoundary : Set where
  field
    weightedValuationSurfaceExists : ⊤
    trackedPrimeSupportIsFinite : ⊤
    valuationDepthIsNotMangoldtWeight : ⊤
    logarithmicLiftNotConstructedHere : ⊤
    allPrimeExtensionNotConstructedHere : ⊤
    noDirectWeightedEnergyToRHPromotion : ⊤

currentWeightedValuationZetaBoundary :
  CurrentWeightedValuationZetaBoundary
currentWeightedValuationZetaBoundary = record
  { weightedValuationSurfaceExists = tt
  ; trackedPrimeSupportIsFinite = tt
  ; valuationDepthIsNotMangoldtWeight = tt
  ; logarithmicLiftNotConstructedHere = tt
  ; allPrimeExtensionNotConstructedHere = tt
  ; noDirectWeightedEnergyToRHPromotion = tt
  }
