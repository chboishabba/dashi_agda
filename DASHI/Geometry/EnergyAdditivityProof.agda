module DASHI.Geometry.EnergyAdditivityProof where

open import Level using (Level; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)
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

record ScalarLaws {ℓ} (F : ScalarField {ℓ}) : Set (suc ℓ) where
  open ScalarField F
  field
    +s-assoc : ∀ a b c → (a +s b) +s c ≡ a +s (b +s c)
    +s-comm  : ∀ a b → a +s b ≡ b +s a
    +s-idL   : ∀ a → 0s +s a ≡ a

open ScalarLaws public

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
  (V : InnerProductSpace A F) (T : Two F) (L : ScalarLaws F) →
  (∀ x y → Orth V x y → ⟪_,_⟫ V x y ≡ 0s F) →
  ∀ x y → Orth V x y → E V ( _+_ A x y ) ≡ ( _+s_ F (E V x) (E V y) )
EnergyAdditivityProof {A = A} {F = F} V T L killCross x y orth =
  let open Additive A
      open ScalarField F
      open InnerProductSpace V
      open ScalarLaws L
      cross0 : ⟪ x , y ⟫ ≡ 0s
      cross0 = killCross x y orth
      cross0' : ⟪ y , x ⟫ ≡ 0s
      cross0' = trans (ip-sym y x) cross0
  in
  trans (E-def (x + y))
        (trans
           (ip-addL x y (x + y))
           (trans
              (cong₂ _+s_ (ip-addR x x y) (ip-addR y x y))
              (let
                  step1 : (⟪ x , x ⟫ +s ⟪ x , y ⟫) +s (⟪ y , x ⟫ +s ⟪ y , y ⟫)
                          ≡ (⟪ x , x ⟫ +s 0s) +s (0s +s ⟪ y , y ⟫)
                  step1 = cong₂ _+s_ (cong (λ t → ⟪ x , x ⟫ +s t) cross0)
                                     (cong (λ t → t +s ⟪ y , y ⟫) cross0')
                  step2 : (⟪ x , x ⟫ +s 0s) +s (0s +s ⟪ y , y ⟫)
                          ≡ (⟪ x , x ⟫ +s 0s) +s ⟪ y , y ⟫
                  step2 = cong (λ t → (⟪ x , x ⟫ +s 0s) +s t) (+s-idL (⟪ y , y ⟫))
                  step3 : (⟪ x , x ⟫ +s 0s) +s ⟪ y , y ⟫
                          ≡ ⟪ x , x ⟫ +s ⟪ y , y ⟫
                  step3 =
                    let leftId : (⟪ x , x ⟫ +s 0s) ≡ ⟪ x , x ⟫
                        leftId = trans (+s-comm (⟪ x , x ⟫) 0s) (+s-idL (⟪ x , x ⟫))
                    in
                    cong (λ t → t +s ⟪ y , y ⟫) leftId
               in
               trans step1 (trans step2 step3))))
