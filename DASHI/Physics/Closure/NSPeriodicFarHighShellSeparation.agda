module DASHI.Physics.Closure.NSPeriodicFarHighShellSeparation where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Constructive natural-number shell separation.
------------------------------------------------------------------------

data _≤shell_ : Nat → Nat → Set where
  zero≤ : ∀ {n} → zero ≤shell n
  suc≤suc : ∀ {m n} → m ≤shell n → suc m ≤shell suc n

≤shell-refl : ∀ n → n ≤shell n
≤shell-refl zero = zero≤
≤shell-refl (suc n) = suc≤suc (≤shell-refl n)

≤shell-trans : ∀ {a b c} → a ≤shell b → b ≤shell c → a ≤shell c
≤shell-trans zero≤ bc = zero≤
≤shell-trans (suc≤suc ab) (suc≤suc bc) =
  suc≤suc (≤shell-trans ab bc)

SeparatedBy : Nat → Nat → Nat → Set
SeparatedBy radius low high = (low + radius) ≤shell high

separationPersistsUnderHigherShell :
  ∀ {radius low high higher} →
  SeparatedBy radius low high →
  high ≤shell higher →
  SeparatedBy radius low higher
separationPersistsUnderHigherShell = ≤shell-trans

farHighShellSeparationLevel : ProofLevel
farHighShellSeparationLevel = machineChecked
