module DASHI.Geometry.EnergyAdditivityProof where

open import Level using (Level; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
open import Data.Unit using (⊤; tt)

record Additive {ℓ} : Set (suc ℓ) where
  field
    Carrier : Set ℓ
    _+_     : Carrier → Carrier → Carrier
    0#      : Carrier
    -_      : Carrier → Carrier

open Additive public

record ScalarField {ℓ} : Set (suc ℓ) where
  field
    Scalar : Set ℓ
    _+s_ _*s_ : Scalar → Scalar → Scalar
    0s 1s : Scalar
    -s_ : Scalar → Scalar

open ScalarField public

record InnerProductSpace {ℓ} (A : Additive {ℓ}) (F : ScalarField {ℓ}) : Set (suc ℓ) where
  open Additive A
  open ScalarField F
  field
    ⟪_,_⟫   : Carrier → Carrier → Scalar
    ip-sym  : ∀ x y → ⟪ x , y ⟫ ≡ ⟪ y , x ⟫
    ip-addL : ∀ x y z → ⟪ x + y , z ⟫ ≡ ⟪ x , z ⟫ +s ⟪ y , z ⟫
    ip-addR : ∀ x y z → ⟪ x , y + z ⟫ ≡ ⟪ x , y ⟫ +s ⟪ x , z ⟫
    ip-negL : ∀ x y → ⟪ - x , y ⟫ ≡ -s ⟪ x , y ⟫
    E       : Carrier → Scalar
    E-def   : ∀ x → E x ≡ ⟪ x , x ⟫

open InnerProductSpace public

Orth : ∀ {ℓ} {A : Additive {ℓ}} {F : ScalarField {ℓ}}
       (V : InnerProductSpace A F) →
       Carrier A → Carrier A → Set ℓ
Orth {A = A} {F = F} V x y = ⟪_,_⟫ V x y ≡ 0s F

record Two {ℓ} (F : ScalarField {ℓ}) : Set (suc ℓ) where
  open ScalarField F
  field
    two : Scalar
    two-def : two ≡ (1s +s 1s)

open Two public

EnergyAdditivityProof :
  ∀ {ℓ}
  {A : Additive {ℓ}} {F : ScalarField {ℓ}}
  (V : InnerProductSpace A F) (T : Two F) →
  (∀ x y → Orth V x y → ⟪_,_⟫ V x y ≡ 0s F) →
  ∀ x y → Orth V x y → E V ( _+_ A x y ) ≡ ( _+s_ F (E V x) (E V y) )
EnergyAdditivityProof {A = A} {F = F} V T _ x y orth =
  let open Additive A
      open ScalarField F
      open InnerProductSpace V
  in
  trans (E-def (x + y))
        {!!}
