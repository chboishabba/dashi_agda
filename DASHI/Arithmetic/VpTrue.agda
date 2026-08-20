module DASHI.Arithmetic.VpTrue where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Nat.Properties using (+-identityʳ; +-suc)
open import Relation.Binary.PropositionalEquality using (trans; sym)

open import DASHI.Arithmetic.VpDepth using
  ( vp-depth
  ; vp-depth-stable-step
  )

------------------------------------------------------------------------
-- Public bounded valuation readout.
--
-- `vp-depth` remains the executable core.  `vp-true p n` keeps the historical
-- self-fuel readout `vp-depth n p n`, but this module NO LONGER postulates that
-- self fuel is globally adequate for every Nat.
--
-- In particular, zero is the familiar p-adic exceptional value: mathematically
-- v_p(0)=+infinity, while the bounded recursion keeps increasing with fuel.
-- Therefore a universal finite plateau theorem must not silently include zero.
--
-- Exact fuel-independence is now proof-relevant: a caller supplies a plateau
-- certificate at the fuel it actually uses, and the constructive stability
-- theorem below propagates that plateau to all larger fuels.
------------------------------------------------------------------------

vp-true : Nat → Nat → Nat
vp-true p n = vp-depth n p n

vp-true-self :
  ∀ p n →
  vp-depth n p n ≡ vp-true p n
vp-true-self _ _ = refl

------------------------------------------------------------------------
-- Constructive plateau propagation.  No global adequacy postulate occurs.
------------------------------------------------------------------------

transport-plateau :
  ∀ fuel p n extra →
  vp-depth fuel p n ≡ vp-depth (suc fuel) p n →
  vp-depth (fuel + extra) p n ≡ vp-depth (suc (fuel + extra)) p n
transport-plateau fuel p n zero plateau
  rewrite +-identityʳ fuel
  = plateau
transport-plateau fuel p n (suc extra) plateau
  rewrite +-suc fuel extra =
  vp-depth-stable-step
    (fuel + extra)
    p
    n
    (transport-plateau fuel p n extra plateau)

plateau-iter :
  ∀ fuel p n extra →
  vp-depth fuel p n ≡ vp-depth (suc fuel) p n →
  vp-depth fuel p n ≡ vp-depth (fuel + extra) p n
plateau-iter fuel p n zero plateau rewrite +-identityʳ fuel = refl
plateau-iter fuel p n (suc extra) plateau
  rewrite +-suc fuel extra =
    trans
      (plateau-iter fuel p n extra plateau)
      (transport-plateau fuel p n extra plateau)

------------------------------------------------------------------------
-- Proof-relevant stabilization certificates.
------------------------------------------------------------------------

record StableVpDepth (p n : Nat) : Set where
  constructor stable-vp-depth
  field
    fuel : Nat
    plateau :
      vp-depth fuel p n ≡ vp-depth (suc fuel) p n

open StableVpDepth public

certified-vp :
  ∀ {p n} → StableVpDepth p n → Nat
certified-vp {p} {n} C = vp-depth (fuel C) p n

certified-vp-stable :
  ∀ {p n} → (C : StableVpDepth p n) → (extra : Nat) →
  vp-depth (fuel C + extra) p n ≡ certified-vp C
certified-vp-stable {p} {n} C extra =
  sym (plateau-iter (fuel C) p n extra (plateau C))

------------------------------------------------------------------------
-- Optional adequacy certificate for the historical self-fuel readout.
------------------------------------------------------------------------

record VpTrueAdequacy (p n : Nat) : Set where
  constructor vp-true-adequacy
  field
    selfFuelPlateau :
      vp-depth n p n ≡ vp-depth (suc n) p n

open VpTrueAdequacy public

vp-true-stable :
  ∀ p n → VpTrueAdequacy p n → (extra : Nat) →
  vp-depth (n + extra) p n ≡ vp-true p n
vp-true-stable p n A extra =
  sym (plateau-iter n p n extra (selfFuelPlateau A))

record VpTrueBoundary : Set where
  field
    executableSelfFuelReadoutRetained : Bool
    globalFuelAdequacyPostulated : Bool
    stabilizationProofRelevant : Bool
    largerFuelStabilityDerivedFromPlateau : Bool
    zeroTreatedAsAutomaticallyFiniteValuation : Bool

canonicalVpTrueBoundary : VpTrueBoundary
canonicalVpTrueBoundary = record
  { executableSelfFuelReadoutRetained = true
  ; globalFuelAdequacyPostulated = false
  ; stabilizationProofRelevant = true
  ; largerFuelStabilityDerivedFromPlateau = true
  ; zeroTreatedAsAutomaticallyFiniteValuation = false
  }
