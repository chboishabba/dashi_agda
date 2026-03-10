{-# OPTIONS --safe #-}

module DASHI.Physics.Signature31 where

-- Prototype-only: this module contains a trivial `sig31` witness used as a
-- placeholder. Canonical closure surfaces must not route signature claims
-- through this module.

open import Level using (Level; suc)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import DASHI.Physics.Core

record Signature : Set where
  field
    p n z : ℕ    -- positive, negative, zero counts

sig31 : Signature
Signature.p sig31 = 3
Signature.n sig31 = 1
Signature.z sig31 = 0

-- Prototype-only signature interface.
--
-- NOTE: this module is intentionally non-theorem-critical. It provides a
-- *trivial* witness packaged as a record, for early plumbing only. Canonical
-- closure consumers must import a theorem-critical seam (e.g.
-- `DASHI.Physics.Signature31FromShiftOrbitProfile`) rather than relying on this.
record SignatureTheorem {ℓ : Level} (V : Set ℓ) : Set (suc ℓ) where
  field
    signature : Quadratic V → Signature

prototypeSignature31Witness :
  ∀ {ℓ} {V : Set ℓ} →
  (Q  : Quadratic V) →
  (ι  : Involution V) →
  (iso : Isotropy V) →
  (fs : FiniteSpeed V) →
  PreservesQuadratic iso Q →
  Σ (SignatureTheorem V) (λ thm → SignatureTheorem.signature thm Q ≡ sig31)
prototypeSignature31Witness _ _ _ _ _ =
  record { signature = λ _ → sig31 } , refl
