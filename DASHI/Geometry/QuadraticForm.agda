module DASHI.Geometry.QuadraticForm where

open import Level using (Level; _⊔_; suc; zero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product using (Σ; _,_)

open import DASHI.Geometry.ProjectionDefect

record ScalarField (ℓ : Level) : Set (suc ℓ) where
  field
    S    : Set ℓ
    _+s_ : S → S → S
    _*s_ : S → S → S
    0s   : S
    1s   : S
    -s_  : S → S

open ScalarField public

record QuadraticForm {ℓv ℓs}
  (A : Additive ℓv) (F : ScalarField ℓs)
  : Set (suc (ℓv ⊔ ℓs)) where
  open Additive A
  open ScalarField F
  field
    Q : Additive.Carrier A → ScalarField.S F
    _·_ : ScalarField.S F → Additive.Carrier A → Additive.Carrier A
    Parallelogram :
      ∀ x y → ScalarField._+s_ F (Q (Additive._+_ A x y))
                                  (Q (Additive._+_ A x (Additive.-_ A y)))
              ≡ ScalarField._+s_ F (ScalarField._+s_ F (Q x) (Q x))
                                   (ScalarField._+s_ F (Q y) (Q y))
    Homog :
      ∀ (a : ScalarField.S F) (x : Additive.Carrier A) →
        Q (_·_ a x)
          ≡
        ScalarField._*s_ F
          (ScalarField._*s_ F a a)
          (Q x)

open QuadraticForm public
