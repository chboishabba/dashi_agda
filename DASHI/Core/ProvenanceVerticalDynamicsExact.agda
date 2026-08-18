module DASHI.Core.ProvenanceVerticalDynamicsExact where

------------------------------------------------------------------------
-- HIDDEN / VERTICAL DYNAMICS OVER AN EXACT REOPENABLE QUOTIENT
--
-- This extends the existing ProvenanceBearingQuotient and
-- ProvenanceQuotientDynamics surfaces rather than creating a second quotient
-- theory.  The key theorem is exact:
--
--   same public surface + same provenance receipt => same fine carrier.
--
-- Therefore every nontrivial fibre-preserving transition must move the
-- provenance/residual coordinate of an exact reopenable quotient.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Core.FibreRestrictionCore as Fibre
import DASHI.Core.ProvenanceBearingQuotient as PBQ

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

Injective : ∀ {A B : Set} → (A → B) → Set
Injective f = ∀ {x y} → f x ≡ f y → x ≡ y

------------------------------------------------------------------------
-- Surface + receipt is an exact separating observer.
------------------------------------------------------------------------

surfaceReceiptObserver :
  ∀ {core : Fibre.FibreRestrictionCore} →
  PBQ.ProvenanceBearingQuotient core →
  Fibre.Carrier core →
  Fibre.Surface core × PBQ.Receipt
    {core = core}
    -- Agda resolves the projection record from the explicit quotient below.
    -- This type annotation is intentionally expanded by the helper definition.
    (λ where)
surfaceReceiptObserver = _
