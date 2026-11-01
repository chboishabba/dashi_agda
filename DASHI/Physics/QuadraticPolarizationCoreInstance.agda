module DASHI.Physics.QuadraticPolarizationCoreInstance where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import Data.Product using (_×_; _,_)

open import Data.Integer using (ℤ; _+_; _-_; _*_; +_; -_)
open import Data.Integer.Properties as IntP
import Data.Integer.Tactic.RingSolver as IntRS
import Tactic.RingSolver.NonReflective as NR

open import Data.Vec using (Vec; []; _∷_)
open import DASHI.Geometry.QuadraticForm
open import DASHI.Geometry.OrthogonalityFromPolarization as OP
open import DASHI.Physics.QuadraticPolarization as QP

open QP.ℤ-Reasoning

module RingZ = NR IntRS.ring
open RingZ using (Expr; Κ; Ι; _⊕_; _⊗_; ⊝_; _⊜_; solve)

-- Scalar field instance for ℤ (minimal, for polarization only).
ScalarFieldℤ : ScalarField _
ScalarFieldℤ =
  record
    { S = ℤ
    ; _+s_ = _+_
    ; _*s_ = _*_
    ; 0s = + 0
    ; 1s = + 1
    ; -s_ = -_
    }

-- Proof: Q̂core(x+y) = Q̂core x + Q̂core y + 2·dot x y  (for ℤ vectors).
square-sum :
  ∀ (x y : ℤ) →
    (x + y) * (x + y) ≡ (x * x + y * y) + ((+ 2) * (x * y))
square-sum x y =
  RingZ.solve 2
    (λ x y →
       ( ((x ⊕ y) ⊗ (x ⊕ y))
       , ((x ⊗ x ⊕ y ⊗ y) ⊕ ((Κ (+ 2)) ⊗ (x ⊗ y))) ))
    refl x y

rearrange :
  ∀ (x2 y2 xy qx qy dot : ℤ) →
    (x2 + y2 + ((+ 2) * xy)) + (qx + qy + ((+ 2) * dot))
      ≡
    (x2 + qx) + (y2 + qy) + ((+ 2) * (xy + dot))
rearrange x2 y2 xy qx qy dot =
  RingZ.solve 6
    (λ x2 y2 xy qx qy dot →
       ( ((x2 ⊕ y2 ⊕ (Κ (+ 2) ⊗ xy)) ⊕ (qx ⊕ qy ⊕ (Κ (+ 2) ⊗ dot)))
       , ((x2 ⊕ qx) ⊕ (y2 ⊕ qy) ⊕ (Κ (+ 2) ⊗ (xy ⊕ dot))) ))
    refl x2 y2 xy qx qy dot

polarization-core :
  ∀ {m : Nat} (x y : Vec ℤ m) →
    QP.Q̂core (QP._+ᵥ_ x y)
      ≡
    (QP.Q̂core x + QP.Q̂core y)
      + ((+ 2) * QP.dotℤ x y)
polarization-core {m = Nat.zero} [] [] = refl
polarization-core {m = Nat.suc n} (x ∷ xs) (y ∷ ys) =
  begin
    QP.Q̂core (QP._+ᵥ_ (x ∷ xs) (y ∷ ys))
  ≡⟨ refl ⟩
    ((x + y) * (x + y)) + QP.Q̂core (QP._+ᵥ_ xs ys)
  ≡⟨ cong (λ t → t + QP.Q̂core (QP._+ᵥ_ xs ys)) (square-sum x y) ⟩
    ((x * x + y * y) + ((+ 2) * (x * y))) + QP.Q̂core (QP._+ᵥ_ xs ys)
  ≡⟨ cong (λ t → ((x * x + y * y) + ((+ 2) * (x * y))) + t)
          (polarization-core xs ys) ⟩
    ((x * x + y * y) + ((+ 2) * (x * y))) +
    ((QP.Q̂core xs + QP.Q̂core ys) + ((+ 2) * QP.dotℤ xs ys))
  ≡⟨ rearrange (x * x) (y * y) (x * y) (QP.Q̂core xs) (QP.Q̂core ys) (QP.dotℤ xs ys) ⟩
    (x * x + QP.Q̂core xs) + (y * y + QP.Q̂core ys) + ((+ 2) * (x * y + QP.dotℤ xs ys))
  ≡⟨ refl ⟩
    (QP.Q̂core (x ∷ xs) + QP.Q̂core (y ∷ ys)) + ((+ 2) * QP.dotℤ (x ∷ xs) (y ∷ ys))
  ∎

-- Polarization instance for Qcoreℤ using the dot product over ℤ.
polarizationCore :
  ∀ {m : Nat} →
  OP.Polarization (record
    { Carrier = Vec ℤ m
    ; _+_ = QP._+ᵥ_
    ; 0# = QP.zeroVecℤ {m}
    ; -_ = λ v → v  -- additive inverse not used in polarization proof here
    })
    ScalarFieldℤ
polarizationCore {m} =
  record
    { Q = QP.Q̂core
    ; ⟪_,_⟫ = QP.dotℤ
    ; two = + 2
    ; two-def = refl
    ; polarization = polarization-core
    }
