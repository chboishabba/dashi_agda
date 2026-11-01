module DASHI.Geometry.ProjectionDefect where

open import Level using (Level; _⊔_; suc; zero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Product using (Σ; _,_)
open import Data.Unit using (⊤; tt)

record Additive (ℓ : Level) : Set (suc ℓ) where
  field
    Carrier : Set ℓ
    _+_     : Carrier → Carrier → Carrier
    0#      : Carrier
    -_      : Carrier → Carrier

open Additive public

record ProjectionDefect {ℓ} (A : Additive ℓ) : Set (suc ℓ) where
  open Additive A
  field
    P     : Additive.Carrier A → Additive.Carrier A
    D     : Additive.Carrier A → Additive.Carrier A
    D-def : ∀ x → D x ≡ Additive._+_ A x (Additive.-_ A (P x))

    P-idem : ∀ x → P (P x) ≡ P x

    Orth : Additive.Carrier A → Additive.Carrier A → Set ℓ
    Orth-PD : ∀ x → Orth (P x) (D x)

open ProjectionDefect public
