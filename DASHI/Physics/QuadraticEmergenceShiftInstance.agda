module DASHI.Physics.QuadraticEmergenceShiftInstance where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)
open import Data.Product using (Σ; _,_; proj₁)
open import Data.Unit using (⊤)
open import Data.Vec using (Vec; []; _∷_; map; zipWith)
import Data.Integer as Int
open Int using (ℤ; _+_; _-_; _*_; +_)
open import Data.Integer.Properties as IntP
import Relation.Binary.Reasoning.Setoid as EqR
import Data.Integer.Tactic.RingSolver as IntRS
import Tactic.RingSolver.NonReflective as NR

import DASHI.Geometry.ProjectionDefect as PD
open import DASHI.Geometry.QuadraticForm as QF
open import DASHI.Geometry.QuadraticFormEmergence as QFE
open import DASHI.Geometry.ProjectionDefectToParallelogram as PDP
open import DASHI.Physics.QuadraticPolarization as QP

module ℤR = EqR IntP.≡-setoid
open ℤR

module RingQ = NR IntRS.ring
open RingQ using (Expr; Κ; Ι; _⊕_; _⊗_; ⊝_; _⊜_; solve)

------------------------------------------------------------------------
-- Additive structure on Vec ℤ m

negVec : ∀ {m} → Vec ℤ m → Vec ℤ m
negVec = map (λ x → Int.-_ x)

addᵥ-zeroʳ : ∀ {m} (v : Vec ℤ m) → QP._+ᵥ_ v (QP.zeroVecℤ {m}) ≡ v
addᵥ-zeroʳ {m} v with v
... | [] = refl
... | x ∷ xs = cong₂ _∷_ (IntP.+-identityʳ x) (addᵥ-zeroʳ xs)

negVec-zero' : (m : Nat) → negVec (QP.zeroVecℤ {m}) ≡ QP.zeroVecℤ {m}
negVec-zero' zero = refl
negVec-zero' (suc m) = cong₂ _∷_ refl (negVec-zero' m)

negVec-zero : ∀ {m} → negVec (QP.zeroVecℤ {m}) ≡ QP.zeroVecℤ {m}
negVec-zero {m} = negVec-zero' m

------------------------------------------------------------------------
-- Scalar field over ℤ (minimal structure for QuadraticFormEmergence)

ScalarFieldℤ : QF.ScalarField _
ScalarFieldℤ =
  record
    { S = ℤ
    ; _+s_ = _+_
    ; _*s_ = _*_
    ; 0s = + 0
    ; 1s = + 1
    ; -s_ = Int.-_
    }

------------------------------------------------------------------------
-- Quadratic energy on Vec ℤ m: sum of squares

Q̂core-zeroVec : ∀ {m} → QP.Q̂core (QP.zeroVecℤ {m}) ≡ + 0
Q̂core-zeroVec {zero} = refl
Q̂core-zeroVec {suc m} =
  cong (λ n → (+ 0 * + 0) + n) (Q̂core-zeroVec {m})

------------------------------------------------------------------------
-- Scalar parallelogram lemma on ℤ

sq : ℤ → ℤ
sq x = x * x

swap-sum : ∀ a x b y → (a + x) + (b + y) ≡ (a + b) + (x + y)
swap-sum a x b y =
  Ring.solve 4
    (λ a x b y →
       ((a ⊕ x) ⊕ (b ⊕ y)) , ((a ⊕ b) ⊕ (x ⊕ y)))
    refl a x b y

parallelogramℤ :
  ∀ a b →
    (sq (a + b) + sq (a - b)) ≡ (sq a + sq a) + (sq b + sq b)
parallelogramℤ a b =
  Ring.solve 2
    (λ x y →
       ( ((x ⊕ y) ⊗ (x ⊕ y)) ⊕ ((x ⊕ (⊝ y)) ⊗ (x ⊕ (⊝ y))) )
       , ( ((x ⊗ x) ⊕ (x ⊗ x)) ⊕ ((y ⊗ y) ⊕ (y ⊗ y)) ))
    refl a b

reassoc :
  ∀ p q r s →
    ((p + p) + (q + q)) + ((r + r) + (s + s))
      ≡
    ((p + r) + (p + r)) + ((q + s) + (q + s))
reassoc p q r s =
  Ring.solve 4
    (λ p q r s →
       ((p ⊕ p) ⊕ (q ⊕ q)) ⊕ ((r ⊕ r) ⊕ (s ⊕ s))
       , ((p ⊕ r) ⊕ (p ⊕ r)) ⊕ ((q ⊕ s) ⊕ (q ⊕ s)))
    refl p q r s

------------------------------------------------------------------------
-- Parallelogram law for QP.Q̂core on Vec ℤ m (by induction)

parallelogramQ̂core :
  ∀ {m} (x y : Vec ℤ m) →
    QP.Q̂core (x +ᵥ y) + QP.Q̂core (x +ᵥ negVec y)
      ≡
    (QP.Q̂core x + QP.Q̂core x) + (QP.Q̂core y + QP.Q̂core y)
parallelogramQ̂core {zero} [] [] = refl
parallelogramQ̂core {suc m} (a ∷ xs) (b ∷ ys) =
  begin
    QP.Q̂core ((a ∷ xs) +ᵥ (b ∷ ys)) + QP.Q̂core ((a ∷ xs) +ᵥ negVec (b ∷ ys))
  ≡⟨ refl ⟩
    ((a + b) * (a + b) + QP.Q̂core (xs +ᵥ ys))
      + ((a - b) * (a - b) + QP.Q̂core (xs +ᵥ negVec ys))
  ≡⟨ swap-sum ((a + b) * (a + b)) (QP.Q̂core (xs +ᵥ ys))
                ((a - b) * (a - b)) (QP.Q̂core (xs +ᵥ negVec ys)) ⟩
    ((a + b) * (a + b) + (a - b) * (a - b))
      + (QP.Q̂core (xs +ᵥ ys) + QP.Q̂core (xs +ᵥ negVec ys))
  ≡⟨ cong (λ t → t + (QP.Q̂core (xs +ᵥ ys) + QP.Q̂core (xs +ᵥ negVec ys)))
        (parallelogramℤ a b) ⟩
    ((a * a + a * a) + (b * b + b * b))
      + (QP.Q̂core (xs +ᵥ ys) + QP.Q̂core (xs +ᵥ negVec ys))
  ≡⟨ cong (λ t → ((a * a + a * a) + (b * b + b * b)) + t)
        (parallelogramQ̂core xs ys) ⟩
    ((a * a + a * a) + (b * b + b * b))
      + ((QP.Q̂core xs + QP.Q̂core xs) + (QP.Q̂core ys + QP.Q̂core ys))
  ≡⟨ reassoc (a * a) (b * b) (QP.Q̂core xs) (QP.Q̂core ys) ⟩
    ((a * a + QP.Q̂core xs) + (a * a + QP.Q̂core xs))
      + ((b * b + QP.Q̂core ys) + (b * b + QP.Q̂core ys))
  ≡⟨ refl ⟩
    (QP.Q̂core (a ∷ xs) + QP.Q̂core (a ∷ xs)) + (QP.Q̂core (b ∷ ys) + QP.Q̂core (b ∷ ys))
  ∎

------------------------------------------------------------------------
-- Projection/defect structure (trivial P, D) to satisfy emergence axioms

AdditiveVecℤ : ∀ {m} → PD.Additive _
AdditiveVecℤ {m} =
  record
    { Carrier = Vec ℤ m
    ; _+_ = QP._+ᵥ_
    ; 0# = QP.zeroVecℤ {m}
    ; -_ = negVec
    }

PDzero : ∀ {m} → PD.ProjectionDefect (AdditiveVecℤ {m})
PDzero {m} =
  record
    { P = λ _ → QP.zeroVecℤ {m}
    ; D = λ x → x
    ; D-def = λ x →
        let
          step1 : x ≡ QP._+ᵥ_ x (negVec (QP.zeroVecℤ {m}))
          step1 = trans (sym (addᵥ-zeroʳ x)) (cong (λ t → QP._+ᵥ_ x t) (sym (negVec-zero {m})))
        in
        step1
    ; P-idem = λ _ → refl
    ; Orth = λ x _ → x ≡ QP.zeroVecℤ {m}
    ; Orth-PD = λ _ → refl
    }

------------------------------------------------------------------------
-- Quadratic emergence axioms for the ℤ-lifted core

QuadraticEmergenceShiftAxioms :
  ∀ {m} →
  QFE.QuadraticEmergenceAxioms
    (AdditiveVecℤ {m})
    ScalarFieldℤ
    (PDzero {m})
QuadraticEmergenceShiftAxioms {m} =
  record
    { Energy = QP.Q̂core
    ; ParallelogramQ = parallelogramQ̂core
    ; Additive-On-Orth = λ x y orth →
        begin
          QP.Q̂core (x +ᵥ y)
        ≡⟨ cong (λ t → QP.Q̂core t) (cong (λ t → t +ᵥ y) orth) ⟩
          QP.Q̂core (QP.zeroVecℤ {m} +ᵥ y)
        ≡⟨ cong QP.Q̂core (QP.zeroVecℤ+ᵥ y) ⟩
          QP.Q̂core y
        ≡⟨ sym (IntP.+-identityˡ (QP.Q̂core y)) ⟩
          (+ 0) + QP.Q̂core y
        ≡⟨ cong (λ t → t + QP.Q̂core y) (sym (Q̂core-zeroVec {m})) ⟩
          QP.Q̂core (QP.zeroVecℤ {m}) + QP.Q̂core y
        ≡⟨ sym (cong (λ t → t + QP.Q̂core y) (cong QP.Q̂core orth)) ⟩
          QP.Q̂core x + QP.Q̂core y
        ∎
    ; PD-splits = λ x →
        begin
          QP.Q̂core x
        ≡⟨ sym (IntP.+-identityˡ (QP.Q̂core x)) ⟩
          (+ 0) + QP.Q̂core x
        ≡⟨ cong (λ t → t + QP.Q̂core x) (sym (Q̂core-zeroVec {m})) ⟩
          QP.Q̂core (QP.zeroVecℤ {m}) + QP.Q̂core x
        ∎
    }

-- Package-first canonical routing helpers for the shift realization.
projectionParallelogramShift :
  ∀ {m} →
  PDP.ProjectionDefectParallelogramPackage
    (AdditiveVecℤ {m}) ScalarFieldℤ
projectionParallelogramShift {m} =
  PDP.fromEmergenceAxioms
    (AdditiveVecℤ {m}) ScalarFieldℤ
    (PDzero {m})
    (QuadraticEmergenceShiftAxioms {m})

quadraticShiftΣ :
  ∀ {m} →
  Σ (QF.QuadraticForm (AdditiveVecℤ {m}) ScalarFieldℤ) (λ _ → ⊤)
quadraticShiftΣ {m} =
  PDP.quadraticFromProjectionDefect
    (AdditiveVecℤ {m}) ScalarFieldℤ
    (projectionParallelogramShift {m})

quadraticShift :
  ∀ {m} →
  QF.QuadraticForm (AdditiveVecℤ {m}) ScalarFieldℤ
quadraticShift {m} = proj₁ (quadraticShiftΣ {m})
