module FascisticSystem where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Data.Nat using (_≤_; _<_)
open import Data.Product using (Σ; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

------------------------------------------------------------------------
-- Legacy contraction core, made mathematically honest.
--
-- A plain idempotent endomap need not collapse anything: identity is the
-- obvious counterexample.  Projection therefore remains the weak algebraic
-- notion, while ProperContraction carries an explicit witness that two
-- distinct fine states are identified.  `distinctionRank` replaces the old
-- misleading name `entropy`; fascistic systems may increase raw records or
-- classifications while destroying recoverable distinctions.
------------------------------------------------------------------------

postulate
  S : Set
  finiteS : Nat
  distinctionRank : S → Nat

record Projection : Set where
  field
    K        : S → S
    idemp    : ∀ s → K (K s) ≡ K s
    contract : ∀ s → distinctionRank (K s) ≤ distinctionRank s

open Projection public

record ProperContraction (projection : Projection) : Set where
  field
    left right : S
    genuinelyDistinct : left ≡ right → ⊥
    collapsed : K projection left ≡ K projection right

open ProperContraction public

properContractionIsNonInjective :
  (projection : Projection) →
  ProperContraction projection →
  (∀ {x y} → K projection x ≡ K projection y → x ≡ y) →
  ⊥
properContractionIsNonInjective projection witness injective =
  genuinelyDistinct witness (injective (collapsed witness))

------------------------------------------------------------------------
-- Global contraction dynamics retained for backwards conceptual continuity.
------------------------------------------------------------------------

postulate
  Ktotal : S → S
  monotone : ∀ s → distinctionRank (Ktotal s) ≤ distinctionRank s
  strict-decrease :
    ∀ s →
    distinctionRank (Ktotal s) < distinctionRank s
    ⊎ (Ktotal s ≡ s)

Attractor : Set
Attractor = Σ S (λ s → Ktotal s ≡ s)

iterate : Nat → S → S
iterate zero    s = s
iterate (suc n) s = Ktotal (iterate n s)

------------------------------------------------------------------------
-- Boundary.
--
-- Proper contraction is a structural witness, not by itself an empirical
-- diagnosis of fascism.  The governance layer separately types erasure,
-- provenance weaponisation, collective-guilt transport, terminalisation and
-- asymmetric routing.
------------------------------------------------------------------------
