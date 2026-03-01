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
    +s-assoc :
      ∀ (a b c : ScalarField.Scalar F) →
      ScalarField._+s_ F (ScalarField._+s_ F a b) c
        ≡
      ScalarField._+s_ F a (ScalarField._+s_ F b c)
    +s-comm  :
      ∀ (a b : ScalarField.Scalar F) →
      ScalarField._+s_ F a b ≡ ScalarField._+s_ F b a
    +s-idL   :
      ∀ (a : ScalarField.Scalar F) →
      ScalarField._+s_ F (ScalarField.0s F) a ≡ a

open ScalarLaws public

record InnerProductSpace {ℓ} (A : Additive {ℓ}) (F : ScalarField {ℓ}) : Set (suc ℓ) where
  open Additive A
  open ScalarField F
  field
    ⟪_,_⟫   : Additive.Carrier A → Additive.Carrier A → ScalarField.Scalar F
    ip-sym  : ∀ x y → ⟪ x , y ⟫ ≡ ⟪ y , x ⟫
    ip-addL : ∀ x y z →
      ⟪ Additive._+_ A x y , z ⟫ ≡
      ScalarField._+s_ F (⟪ x , z ⟫) (⟪ y , z ⟫)
    ip-addR : ∀ x y z →
      ⟪ x , Additive._+_ A y z ⟫ ≡
      ScalarField._+s_ F (⟪ x , y ⟫) (⟪ x , z ⟫)
    ip-negL : ∀ x y →
      ⟪ Additive.-_ A x , y ⟫ ≡ ScalarField.-s_ F (⟪ x , y ⟫)
    E       : Additive.Carrier A → ScalarField.Scalar F
    E-def   : ∀ x → E x ≡ ⟪ x , x ⟫

open InnerProductSpace public

Orth : ∀ {ℓ} {A : Additive {ℓ}} {F : ScalarField {ℓ}}
       (V : InnerProductSpace A F) →
       Carrier A → Carrier A → Set ℓ
Orth {A = A} {F = F} V x y = ⟪_,_⟫ V x y ≡ 0s F

record Two {ℓ} (F : ScalarField {ℓ}) : Set (suc ℓ) where
  open ScalarField F
  field
    two : ScalarField.Scalar F
    two-def : two ≡ ScalarField._+s_ F (ScalarField.1s F) (ScalarField.1s F)

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
      infixl 6 _⊕_
      _⊕_ : ScalarField.Scalar F → ScalarField.Scalar F → ScalarField.Scalar F
      _⊕_ = ScalarField._+s_ F
      ip : Additive.Carrier A → Additive.Carrier A → ScalarField.Scalar F
      ip = InnerProductSpace.⟪_,_⟫ V
      cross0 : ip x y ≡ ScalarField.0s F
      cross0 = killCross x y orth
      cross0' : ip y x ≡ ScalarField.0s F
      cross0' = trans (InnerProductSpace.ip-sym V y x) cross0
  in
  trans (InnerProductSpace.E-def V (Additive._+_ A x y))
        (trans
           (InnerProductSpace.ip-addL V x y (Additive._+_ A x y))
           (trans
              (cong₂ (ScalarField._+s_ F) (InnerProductSpace.ip-addR V x x y) (InnerProductSpace.ip-addR V y x y))
              (let
                  step1 : (ip x x ⊕ ip x y) ⊕ (ip y x ⊕ ip y y)
                          ≡ (ip x x ⊕ ScalarField.0s F) ⊕ (ScalarField.0s F ⊕ ip y y)
                  step1 = cong₂ _⊕_ (cong (λ t → ip x x ⊕ t) cross0)
                                    (cong (λ t → t ⊕ ip y y) cross0')
                  step2 : (ip x x ⊕ ScalarField.0s F) ⊕ (ScalarField.0s F ⊕ ip y y)
                          ≡ (ip x x ⊕ ScalarField.0s F) ⊕ ip y y
                  step2 = cong (λ t → (ip x x ⊕ ScalarField.0s F) ⊕ t) (ScalarLaws.+s-idL L (ip y y))
                  step3 : (ip x x ⊕ ScalarField.0s F) ⊕ ip y y
                          ≡ ip x x ⊕ ip y y
                  step3 =
                    let leftId : (ip x x ⊕ ScalarField.0s F) ≡ ip x x
                        leftId = trans (ScalarLaws.+s-comm L (ip x x) (ScalarField.0s F))
                                      (ScalarLaws.+s-idL L (ip x x))
                    in
                    cong (λ t → t ⊕ ip y y) leftId
                  step4 : ip x x ⊕ ip y y ≡ InnerProductSpace.E V x ⊕ InnerProductSpace.E V y
                  step4 = cong₂ _⊕_ (sym (InnerProductSpace.E-def V x))
                                       (sym (InnerProductSpace.E-def V y))
               in
               trans step1 (trans step2 (trans step3 step4)))))
