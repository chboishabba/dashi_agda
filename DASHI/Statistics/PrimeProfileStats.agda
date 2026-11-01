module DASHI.Statistics.PrimeProfileStats where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import Ontology.GodelLattice using (FactorVec)
open import Ontology.GodelLattice renaming (v15 to mkVec15)
open import Ontology.Hecke.FactorVecInstances using
  (SupportMask; supportMask)
open import DASHI.Arithmetic.PrimeIndexedPressure using
  (PrimeContributionVec; sum15)

------------------------------------------------------------------------
-- Prime-profile stats over the repo-native FactorVec carrier.
--
-- The module stays intentionally thin:
-- - the carrier is FactorVec
-- - the existing supportMask projection is reused
-- - a numeric Vec15 Nat view is derived from that mask
-- - one score helper exposes the summed profile

boolToNat : Bool → Nat
boolToNat false = zero
boolToNat true = suc zero

supportMaskWeights : SupportMask → PrimeContributionVec
supportMaskWeights (mkVec15 b2 b3 b5 b7 b11 b13 b17 b19 b23 b29 b31 b41 b47 b59 b71) =
  mkVec15 (boolToNat b2) (boolToNat b3) (boolToNat b5) (boolToNat b7)
          (boolToNat b11) (boolToNat b13) (boolToNat b17) (boolToNat b19)
          (boolToNat b23) (boolToNat b29) (boolToNat b31) (boolToNat b41)
          (boolToNat b47) (boolToNat b59) (boolToNat b71)

record PrimeProfileStats : Set₁ where
  field
    carrier : FactorVec
    carrierMask : SupportMask
    carrierWeights : PrimeContributionVec
    carrierMaskMatches :
      carrierMask ≡ supportMask carrier
    carrierWeightsMatches :
      carrierWeights ≡ supportMaskWeights carrierMask

primeProfileStats : FactorVec → PrimeProfileStats
primeProfileStats v = record
  { carrier = v
  ; carrierMask = supportMask v
  ; carrierWeights = supportMaskWeights (supportMask v)
  ; carrierMaskMatches = refl
  ; carrierWeightsMatches = refl
  }

primeProfileMask : PrimeProfileStats → SupportMask
primeProfileMask = PrimeProfileStats.carrierMask

primeProfileWeights : PrimeProfileStats → PrimeContributionVec
primeProfileWeights = PrimeProfileStats.carrierWeights

primeProfileScore : PrimeProfileStats → Nat
primeProfileScore s = sum15 (primeProfileWeights s)

open PrimeProfileStats public
