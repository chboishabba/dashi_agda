module DASHI.Moonshine.Y443FLMWeightTwoBasisUVExact where

-- Exact finite generating-basis reduction of the remaining u/v equations.
-- A basis must be a spanning family of the ACTUAL selected V_2, not a
-- cardinality match or a 196884-element set of unnamed coordinate tags.
-- No numeric matrix entries or actual Monster representation are fabricated.

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin.Base using (Fin)

import DASHI.Moonshine.VertexOperatorAlgebraCore as VOA
import DASHI.Moonshine.Y443FLMGriessFullAutSelectedVOAExact as FLM

sym : ∀ {X : Set} {a b : X} → a ≡ b → b ≡ a
sym refl = refl

trans : ∀ {X : Set} {a b c : X} → a ≡ b → b ≡ c → a ≡ c
trans refl q = q

cong : ∀ {X Y : Set} (f : X → Y) {a b : X} → a ≡ b → f a ≡ f b
cong f refl = refl

cong₂ : ∀ {X Y Z : Set} (f : X → Y → Z)
  {a b : X} {c d : Y} →
  a ≡ b → c ≡ d → f a c ≡ f b d
cong₂ f refl refl = refl

module Selected (V : VOA.VertexOperatorAlgebra) where
  module A = FLM.Selected V

  module WithGriess (griess : A.ConcreteGriessProduct) where

    -- Only source constants, addition and scalar multiplication.
    -- Do not assume (a priori) that the list is linearly independent;
    -- spanning is sufficient for the equality-of-maps theorem.
    data LinearTerm : Set where
      basis : Fin 196884 → LinearTerm
      sumTerm : LinearTerm → LinearTerm → LinearTerm
      scaleTerm : A.Scalar → LinearTerm → LinearTerm

    record ActualWeightTwoSpan : Setω where
      field
        basisState : Fin 196884 → A.WeightTwo
        evaluate : LinearTerm → A.WeightTwo
        evaluateBasis : (i : Fin 196884) →
          evaluate (basis i) ≡ basisState i
        evaluateSum : (l r : LinearTerm) →
          evaluate (sumTerm l r) ≡
          A.weightTwoAdd griess (evaluate l) (evaluate r)
        evaluateScale : (s : A.Scalar) (l : LinearTerm) →
          evaluate (scaleTerm s l) ≡
          A.weightTwoScale griess s (evaluate l)
        expressionFor : A.WeightTwo → LinearTerm
        expressionEvaluates : (x : A.WeightTwo) →
          evaluate (expressionFor x) ≡ x
    open ActualWeightTwoSpan public

    agreementOnTerm :
      (span : ActualWeightTwoSpan)
      (left right : A.SelectedVOAAutomorphism) →
      ((i : Fin 196884) →
        A.weightTwoAction left (basisState span i)
        ≡ A.weightTwoAction right (basisState span i)) →
      (t : LinearTerm) →
      A.weightTwoAction left (evaluate span t)
      ≡ A.weightTwoAction right (evaluate span t)
    agreementOnTerm span left right eq (basis i) =
      trans
        (cong (A.weightTwoAction left)
          (evaluateBasis span i))
        (trans
          (eq i)
          (sym (cong (A.weightTwoAction right)
            (evaluateBasis span i))))
    agreementOnTerm span left right eq (sumTerm l r) =
      trans
        (cong (A.weightTwoAction left) (evaluateSum span l r))
        (trans
          (A.restrictedAdditiveLaw griess left
            (evaluate span l) (evaluate span r))
          (trans
            (cong₂ (A.weightTwoAdd griess)
              (agreementOnTerm span left right eq l)
              (agreementOnTerm span left right eq r))
            (trans
              (sym (A.restrictedAdditiveLaw griess right
                (evaluate span l) (evaluate span r)))
              (sym (cong (A.weightTwoAction right)
                (evaluateSum span l r))))))
    agreementOnTerm span left right eq (scaleTerm s l) =
      trans
        (cong (A.weightTwoAction left) (evaluateScale span s l))
        (trans
          (A.restrictedScalarLaw griess left s (evaluate span l))
          (trans
            (cong (A.weightTwoScale griess s)
              (agreementOnTerm span left right eq l))
            (trans
              (sym (A.restrictedScalarLaw griess right s
                (evaluate span l)))
              (sym (cong (A.weightTwoAction right)
                (evaluateScale span s l))))))

    agreementOnAllWeightTwo :
      (span : ActualWeightTwoSpan)
      (left right : A.SelectedVOAAutomorphism) →
      ((i : Fin 196884) →
        A.weightTwoAction left (basisState span i)
        ≡ A.weightTwoAction right (basisState span i)) →
      (x : A.WeightTwo) →
      A.weightTwoAction left x ≡ A.weightTwoAction right x
    agreementOnAllWeightTwo span left right eq x =
      trans
        (sym (cong (A.weightTwoAction left)
          (expressionEvaluates span x)))
        (trans
          (agreementOnTerm span left right eq (expressionFor span x))
          (cong (A.weightTwoAction right)
            (expressionEvaluates span x)))
