module DASHI.Physics.QuadForcingScaling where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Data.Nat using (ℕ; _<_)

record _↔_ {ℓ₁ ℓ₂ : Level} (A : Set ℓ₁) (B : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  constructor intro
  field
    to   : A → B
    from : B → A

open _↔_ public

record PrincipalScaling : Set₁ where
  field
    σ  : ℕ
    σc : ℕ

open PrincipalScaling public

record QuadraticSource (ℓ : Level) : Set (lsuc ℓ) where
  field
    Field          : Set ℓ
    source         : Field → Field
    quadraticLaw   : Set ℓ
    energyCompatible : Set ℓ

open QuadraticSource public

record LocalWellPosedness {ℓ : Level}
  (Q : QuadraticSource ℓ) : Set (lsuc ℓ) where
  field
    existence   : Set ℓ
    uniqueness  : Set ℓ
    continuation : Set ℓ

open LocalWellPosedness public

energySubcritical :
  PrincipalScaling → Set
energySubcritical S = σ S < σc S

postulate
  quadratic-forcing-wellposedness :
    ∀ {ℓ : Level} →
    (S : PrincipalScaling) →
    (Q : QuadraticSource ℓ) →
    energySubcritical S ↔ LocalWellPosedness Q
