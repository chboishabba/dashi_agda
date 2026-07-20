module DASHI.Physics.Closure.PrimeWeightedQuadraticForm where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
open import Data.Vec using (Vec; []; _∷_)
import Data.Integer as Int
open Int using (ℤ; _+_; _-_; _*_; +_)
open import Data.Integer.Properties as IntP
import Relation.Binary.Reasoning.Setoid as EqR
import Data.Integer.Tactic.RingSolver as IntRS
import Tactic.RingSolver.NonReflective as NR

open import DASHI.Geometry.QuadraticForm as QF
open import DASHI.Physics.QuadraticEmergenceShiftInstance as QES
open import DASHI.Physics.QuadraticPolarization as QP

module ℤReasonPWQ = EqR IntP.≡-setoid
open ℤReasonPWQ

module RingPWQ = NR IntRS.ring
open RingPWQ using (Κ; Ι; _⊕_; _⊗_; ⊝_; solve)

------------------------------------------------------------------------
-- Diagonal weighted quadratic geometry over the existing Vec ℤ carrier.
--
-- This is the exact integer replacement for the informal square-root
-- coordinate sketch.  A weight vector w defines
--
--   Q_w(x) = Σᵢ wᵢ xᵢ².
--
-- No square-root scalar extension is needed, and the result is a genuine
-- `QuadraticForm` in the existing DASHI geometry hierarchy.

weightedQ : ∀ {m : Nat} → Vec ℤ m → Vec ℤ m → ℤ
weightedQ [] [] = + 0
weightedQ (w ∷ ws) (x ∷ xs) = (w * (x * x)) + weightedQ ws xs

weightedHeadParallelogram :
  ∀ w x y →
    (w * ((x + y) * (x + y))) + (w * ((x - y) * (x - y)))
    ≡
    ((w * (x * x)) + (w * (x * x)))
      + ((w * (y * y)) + (w * (y * y)))
weightedHeadParallelogram w x y =
  RingPWQ.solve 3
    (λ w x y →
      ( (w ⊗ ((x ⊕ y) ⊗ (x ⊕ y)))
          ⊕ (w ⊗ ((x ⊕ (⊝ y)) ⊗ (x ⊕ (⊝ y))))
      , ((w ⊗ (x ⊗ x)) ⊕ (w ⊗ (x ⊗ x)))
          ⊕ ((w ⊗ (y ⊗ y)) ⊕ (w ⊗ (y ⊗ y))) ))
    refl w x y

weightedParallelogram :
  ∀ {m : Nat} (weights x y : Vec ℤ m) →
    weightedQ weights (QP._+ᵥ_ x y)
      + weightedQ weights (QP._+ᵥ_ x (QES.negVec y))
    ≡
    (weightedQ weights x + weightedQ weights x)
      + (weightedQ weights y + weightedQ weights y)
weightedParallelogram [] [] [] = refl
weightedParallelogram (w ∷ ws) (x ∷ xs) (y ∷ ys) =
  begin
    weightedQ (w ∷ ws) (QP._+ᵥ_ (x ∷ xs) (y ∷ ys))
      + weightedQ (w ∷ ws) (QP._+ᵥ_ (x ∷ xs) (QES.negVec (y ∷ ys)))
  ≡⟨ refl ⟩
    (w * ((x + y) * (x + y)) + weightedQ ws (QP._+ᵥ_ xs ys))
      + (w * ((x - y) * (x - y))
          + weightedQ ws (QP._+ᵥ_ xs (QES.negVec ys)))
  ≡⟨ QES.swap-sum
        (w * ((x + y) * (x + y)))
        (weightedQ ws (QP._+ᵥ_ xs ys))
        (w * ((x - y) * (x - y)))
        (weightedQ ws (QP._+ᵥ_ xs (QES.negVec ys))) ⟩
    ((w * ((x + y) * (x + y))) + (w * ((x - y) * (x - y))))
      + (weightedQ ws (QP._+ᵥ_ xs ys)
          + weightedQ ws (QP._+ᵥ_ xs (QES.negVec ys)))
  ≡⟨ cong
        (λ t → t +
          (weightedQ ws (QP._+ᵥ_ xs ys)
            + weightedQ ws (QP._+ᵥ_ xs (QES.negVec ys))))
        (weightedHeadParallelogram w x y) ⟩
    (((w * (x * x)) + (w * (x * x)))
      + ((w * (y * y)) + (w * (y * y))))
      + (weightedQ ws (QP._+ᵥ_ xs ys)
          + weightedQ ws (QP._+ᵥ_ xs (QES.negVec ys)))
  ≡⟨ cong
        (λ t →
          (((w * (x * x)) + (w * (x * x)))
            + ((w * (y * y)) + (w * (y * y)))) + t)
        (weightedParallelogram ws xs ys) ⟩
    (((w * (x * x)) + (w * (x * x)))
      + ((w * (y * y)) + (w * (y * y))))
      + ((weightedQ ws xs + weightedQ ws xs)
          + (weightedQ ws ys + weightedQ ws ys))
  ≡⟨ QES.reassoc
        (w * (x * x))
        (w * (y * y))
        (weightedQ ws xs)
        (weightedQ ws ys) ⟩
    ((w * (x * x) + weightedQ ws xs)
      + (w * (x * x) + weightedQ ws xs))
      + ((w * (y * y) + weightedQ ws ys)
          + (w * (y * y) + weightedQ ws ys))
  ∎

weightedHeadHomogeneous :
  ∀ a w x →
    w * ((a * x) * (a * x)) ≡ (a * a) * (w * (x * x))
weightedHeadHomogeneous a w x =
  RingPWQ.solve 3
    (λ a w x →
      ( w ⊗ ((a ⊗ x) ⊗ (a ⊗ x))
      , (a ⊗ a) ⊗ (w ⊗ (x ⊗ x)) ))
    refl a w x

weightedHomogeneous :
  ∀ {m : Nat} (weights : Vec ℤ m) (a : ℤ) (x : Vec ℤ m) →
    weightedQ weights (QES.scaleVec a x)
    ≡
    (a * a) * weightedQ weights x
weightedHomogeneous [] a [] = sym (IntP.*-zeroʳ (a * a))
weightedHomogeneous (w ∷ ws) a (x ∷ xs) =
  begin
    weightedQ (w ∷ ws) (QES.scaleVec a (x ∷ xs))
  ≡⟨ refl ⟩
    w * ((a * x) * (a * x)) + weightedQ ws (QES.scaleVec a xs)
  ≡⟨ cong
        (λ t → t + weightedQ ws (QES.scaleVec a xs))
        (weightedHeadHomogeneous a w x) ⟩
    (a * a) * (w * (x * x)) + weightedQ ws (QES.scaleVec a xs)
  ≡⟨ cong
        (λ t → (a * a) * (w * (x * x)) + t)
        (weightedHomogeneous ws a xs) ⟩
    (a * a) * (w * (x * x)) + (a * a) * weightedQ ws xs
  ≡⟨ sym (IntP.*-distribˡ-+ (a * a) (w * (x * x)) (weightedQ ws xs)) ⟩
    (a * a) * (w * (x * x) + weightedQ ws xs)
  ∎

weightedQuadraticForm :
  ∀ {m : Nat} →
  Vec ℤ m →
  QF.QuadraticForm (QES.AdditiveVecℤ {m}) QES.ScalarFieldℤ
weightedQuadraticForm weights =
  record
    { Q = weightedQ weights
    ; _·_ = QES.scaleVec
    ; Parallelogram = weightedParallelogram weights
    ; Homog = weightedHomogeneous weights
    }

------------------------------------------------------------------------
-- Canonical tracked-prime diagonal form.

primeWeightsℤ : Vec ℤ 15
primeWeightsℤ =
  + 2 ∷ + 3 ∷ + 5 ∷ + 7 ∷ + 11 ∷ + 13 ∷ + 17 ∷ + 19 ∷
  + 23 ∷ + 29 ∷ + 31 ∷ + 41 ∷ + 47 ∷ + 59 ∷ + 71 ∷ []

primeWeightedQuadraticForm :
  QF.QuadraticForm (QES.AdditiveVecℤ {15}) QES.ScalarFieldℤ
primeWeightedQuadraticForm = weightedQuadraticForm primeWeightsℤ
