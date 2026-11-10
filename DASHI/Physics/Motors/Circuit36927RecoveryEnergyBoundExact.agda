module DASHI.Physics.Motors.Circuit36927RecoveryEnergyBoundExact where

------------------------------------------------------------------------
-- Abstract nonnegative integer energy accounting (energy quanta).
-- This is a *conditional* theorem about a specified ledger, not a
-- physical observation of a Resonate369/Slobodian machine.
-- Nat units can represent exactly quantified energy on a chosen grid.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

data _≤_ : Nat → Nat → Set where
  z≤n : ∀ {n} → zero ≤ n
  s≤s : ∀ {m n} → m ≤ n → suc m ≤ suc n

≤-append : (m n : Nat) → m ≤ m + n
≤-append zero n = z≤n
≤-append (suc m) n = s≤s (≤-append m n)

-- Equality transport is explicit, avoiding any unjustified appeal to
-- conservation for a real-world apparatus.
transportUpper :
  ∀ {a b c : Nat} → b ≡ c → a ≤ b → a ≤ c
transportUpper refl proof = proof

record PassiveRecoveryReceipt : Set where
  constructor passiveRecoveryReceipt
  field
    initialStored : Nat
    finalStored : Nat
    heatAndLoss : Nat
    closedBoundaryBalance :
      initialStored ≡ finalStored + heatAndLoss

-- No outside work or source energy is admitted at this boundary.
-- Under that condition, final stored energy cannot exceed initial.
passiveFinalNoGreater :
  (r : PassiveRecoveryReceipt) →
  PassiveRecoveryReceipt.finalStored r ≤
  PassiveRecoveryReceipt.initialStored r
passiveFinalNoGreater r =
  transportUpper
    (sym (PassiveRecoveryReceipt.closedBoundaryBalance r))
    (≤-append (PassiveRecoveryReceipt.finalStored r)
              (PassiveRecoveryReceipt.heatAndLoss r))
