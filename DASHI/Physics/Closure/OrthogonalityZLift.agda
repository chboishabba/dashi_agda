module DASHI.Physics.Closure.OrthogonalityZLift where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong)

open import Data.Integer using (ℤ; _+_; _*_; +_)
open import Data.Integer.Properties as IntP
open import Data.Vec using (Vec; []; _∷_)

open import DASHI.Geometry.OrthogonalityFromPolarization as OP
open import DASHI.Physics.QuadraticPolarization as QP
open import DASHI.Physics.QuadraticPolarizationCoreInstance as QPCI

open QP.ℤ-Reasoning

-- Simple orthogonality seam on the ℤ-lifted carrier.
record OrthogonalityZLift {m : Nat} : Set₁ where
  field
    pol : OP.Polarization (record
      { Carrier = Vec ℤ m
      ; _+_ = QP._+ᵥ_
      ; 0# = QP.zeroVecℤ {m}
      ; -_ = λ v → v
      })
      QPCI.ScalarFieldℤ
    Orth : Vec ℤ m → Vec ℤ m → Set
    Orth-def : ∀ x y → Orth x y ≡ (OP.Polarization.⟪_,_⟫ pol x y ≡ (+ 0))
    orthPD : ∀ x → Orth (QP.zeroVecℤ {m}) x

open OrthogonalityZLift public

-- dotℤ with zero left is zero
Dot-zeroL : ∀ {m : Nat} (x : Vec ℤ m) → QP.dotℤ (QP.zeroVecℤ {m}) x ≡ (+ 0)
Dot-zeroL {zero} [] = refl
Dot-zeroL {suc m} (x ∷ xs) =
  begin
    QP.dotℤ (QP.zeroVecℤ {suc m}) (x ∷ xs)
  ≡⟨ refl ⟩
    ((+ 0) * x) + QP.dotℤ (QP.zeroVecℤ {m}) xs
  ≡⟨ cong (λ t → t + QP.dotℤ (QP.zeroVecℤ {m}) xs) (IntP.*-zeroˡ x) ⟩
    (+ 0) + QP.dotℤ (QP.zeroVecℤ {m}) xs
  ≡⟨ cong (λ t → (+ 0) + t) (Dot-zeroL {m} xs) ⟩
    (+ 0) + (+ 0)
  ≡⟨ IntP.+-identityʳ (+ 0) ⟩
    (+ 0)
  ∎

orthogonalityZLift : ∀ {m : Nat} → OrthogonalityZLift {m}
orthogonalityZLift {m} =
  record
    { pol = QPCI.polarizationCore {m}
    ; Orth = λ x y → QP.dotℤ x y ≡ (+ 0)
    ; Orth-def = λ x y → refl
    ; orthPD = λ x → Dot-zeroL {m} x
    }
