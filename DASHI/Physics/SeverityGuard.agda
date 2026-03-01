module DASHI.Physics.SeverityGuard where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Nat using (_≤_; _<_)

open import UFTC_Lattice as UFTC using (Code; Severity; severity; _⊑_)

-- A severity-based guard policy derived from UFTC_Lattice.Code.
record SeverityPolicy {ℓ} (X : Set ℓ) : Set (lsuc ℓ) where
  field
    code : X → Code
    safeThreshold : Severity
    brokenThreshold : Severity

  Guard : X → Set
  Guard x = severity (code x) ⊑ safeThreshold

  Snap : X → Set
  Snap x = safeThreshold < severity (code x)

  Broken : X → Set
  Broken x = brokenThreshold ⊑ severity (code x)

open SeverityPolicy public

-- Optional: monotonicity helper if you aggregate codes by max severity.
record SeverityAggregator {ℓ} (X : Set ℓ) : Set (lsuc ℓ) where
  field
    policy : SeverityPolicy X
    combine : X → X → X

    -- Combining states preserves (or increases) severity.
    combine-mono :
      ∀ x y →
      severity (SeverityPolicy.code policy x) ⊑
      severity (SeverityPolicy.code policy (combine x y))

open SeverityAggregator public
