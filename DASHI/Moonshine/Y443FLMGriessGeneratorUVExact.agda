module DASHI.Moonshine.Y443FLMGriessGeneratorUVExact where

------------------------------------------------------------------------
-- STRONGER THAN 196884-BASIS GATE: ANY TRUE GRIESS GENERATOR FAMILY.
--
-- If a source-proven family of Griess algebra elements generates V_2 under
-- addition, scalar multiplication and mode-one first product, THEN
-- comparing u/v automorphisms only on those generators suffices.
-- Basis-independent; avoids giant matrices if fewer algebra generators
-- can be source-proved. No assumption about axes or generating cardinality.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)

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

    record TrueGriessGeneratingFamily : Setω where
      field
        Generator : Set
        seed : Generator → A.WeightTwo

      data Expression : Set where
        atom : Generator → Expression
        sum : Expression → Expression → Expression
        scale : A.Scalar → Expression → Expression
        product : Expression → Expression → Expression

      evaluate : Expression → A.WeightTwo
      evaluate (atom g) = seed g
      evaluate (sum x y) =
        A.weightTwoAdd griess (evaluate x) (evaluate y)
      evaluate (scale s x) =
        A.weightTwoScale griess s (evaluate x)
      evaluate (product x y) =
        A.firstProduct griess (evaluate x) (evaluate y)

      field
        -- Must be real source-backed generation, not merely labels.
        expressionFor : A.WeightTwo → Expression
        expressionEvaluates : (x : A.WeightTwo) →
          evaluate (expressionFor x) ≡ x
    open TrueGriessGeneratingFamily public

    generatorAgreementPropagates :
      (family : TrueGriessGeneratingFamily)
      (left right : A.SelectedVOAAutomorphism) →
      ((g : Generator family) →
        A.weightTwoAction left (seed family g)
        ≡ A.weightTwoAction right (seed family g)) →
      (t : Expression family) →
      A.weightTwoAction left (evaluate family t)
      ≡ A.weightTwoAction right (evaluate family t)
    generatorAgreementPropagates family left right eq (atom g) = eq g
    generatorAgreementPropagates family left right eq (sum x y) =
      trans
        (A.restrictedAdditiveLaw griess left
          (evaluate family x) (evaluate family y))
        (trans
          (cong₂ (A.weightTwoAdd griess)
            (generatorAgreementPropagates family left right eq x)
            (generatorAgreementPropagates family left right eq y))
          (sym (A.restrictedAdditiveLaw griess right
            (evaluate family x) (evaluate family y))))
    generatorAgreementPropagates family left right eq (scale s x) =
      trans
        (A.restrictedScalarLaw griess left s (evaluate family x))
        (trans
          (cong (A.weightTwoScale griess s)
            (generatorAgreementPropagates family left right eq x))
          (sym (A.restrictedScalarLaw griess right s
            (evaluate family x))))
    generatorAgreementPropagates family left right eq (product x y) =
      trans
        (A.restrictedProductLaw griess left
          (evaluate family x) (evaluate family y))
        (trans
          (cong₂ (A.firstProduct griess)
            (generatorAgreementPropagates family left right eq x)
            (generatorAgreementPropagates family left right eq y))
          (sym (A.restrictedProductLaw griess right
            (evaluate family x) (evaluate family y))))

    generatorAgreementIsWholeWeightTwo :
      (family : TrueGriessGeneratingFamily)
      (left right : A.SelectedVOAAutomorphism) →
      ((g : Generator family) →
        A.weightTwoAction left (seed family g)
        ≡ A.weightTwoAction right (seed family g)) →
      (x : A.WeightTwo) →
      A.weightTwoAction left x ≡ A.weightTwoAction right x
    generatorAgreementIsWholeWeightTwo family left right eq x =
      trans
        (sym (cong (A.weightTwoAction left)
          (expressionEvaluates family x)))
        (trans
          (generatorAgreementPropagates family left right eq
            (expressionFor family x))
          (cong (A.weightTwoAction right)
            (expressionEvaluates family x)))
