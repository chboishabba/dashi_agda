module AntiFascistSystem where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_≤_)
open import Data.Nat.Properties using (≤-refl)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

------------------------------------------------------------------------
-- Legacy antifascist core, repaired.
--
-- The previous version simultaneously postulated
--
--   H (U x) = H x
--
-- and
--
--   ¬ (∀ x -> H (U x) ≤ H x),
--
-- which is inconsistent because equality implies ≤.  The corrected core does
-- not identify antifascism with generic entropy growth.  It records the exact
-- structural property that an invertible transformation preserves: distinct
-- states remain recoverable, hence U is injective.
------------------------------------------------------------------------

postulate
  S : Set
  distinctionRank : S → Nat

record Invertible : Set where
  field
    U    : S → S
    U⁻¹  : S → S
    left  : ∀ s → U⁻¹ (U s) ≡ s
    right : ∀ s → U (U⁻¹ s) ≡ s

open Invertible public

invertibleInjective :
  (u : Invertible) →
  ∀ {x y} → U u x ≡ U u y → x ≡ y
invertibleInjective u {x} {y} equality =
  trans
    (sym (left u x))
    (trans (cong (U⁻¹ u) equality) (left u y))

record DistinctionPreserving (u : Invertible) : Set where
  field
    rankPreserved : ∀ s → distinctionRank (U u s) ≡ distinctionRank s

open DistinctionPreserving public

rankPreservationImpliesNonincrease :
  (u : Invertible) →
  DistinctionPreserving u →
  ∀ s → distinctionRank (U u s) ≤ distinctionRank s
rankPreservationImpliesNonincrease u preservation s
  rewrite rankPreserved preservation s = ≤-refl

------------------------------------------------------------------------
-- Boundary.
--
-- Invertibility is not asserted to be the complete definition of political
-- antifascism.  It is the exact algebraic anti-collapse property of this
-- legacy toy carrier.  The richer governance modules separately type
-- provenance routing, culpability locality, revision and terminalisation.
------------------------------------------------------------------------
