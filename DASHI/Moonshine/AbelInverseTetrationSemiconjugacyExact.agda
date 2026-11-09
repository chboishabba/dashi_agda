{-# OPTIONS --safe #-}
module DASHI.Moonshine.AbelInverseTetrationSemiconjugacyExact where

-- A constructive *reduction* of the Abel equation to a selected
-- left/right inverse tetration chart; NOT a construction of Kneser's F.
-- Works on arbitrary carriers, including non-Archimedean and hypercomplex.

open import Agda.Primitive using (Set; Set₁)
open import Agda.Builtin.Equality using (_≡_; refl)

private
  variable A B : Set

cong : (f : A → B) → {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

trans : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

record InverseTetrationChart : Set₁ where
  field
    Height : Set
    Value : Set
    successor : Height → Height
    exponential : Value → Value
    tetration : Height → Value
    abel : Value → Height

    tetrationStep :
      (h : Height) →
      tetration (successor h) ≡ exponential (tetration h)
    abelTetration :
      (h : Height) → abel (tetration h) ≡ h
    tetrationAbel :
      (w : Value) → tetration (abel w) ≡ w

open InverseTetrationChart public

abelExponentialFromInverseTetration :
  (C : InverseTetrationChart) →
  (w : Value C) →
  abel C (exponential C w) ≡ successor C (abel C w)
abelExponentialFromInverseTetration C w =
  trans
    (cong (λ v → abel C (exponential C v))
      (symLocal (tetrationAbel C w)))
    (trans
      (cong (abel C) (symLocal (tetrationStep C (abel C w))))
      (abelTetration C (successor C (abel C w))))

symLocal : {x y : A} → x ≡ y → y ≡ x
symLocal refl = refl

-- Converse: if the Abel coordinate has an inverse and satisfies its
-- functional equation, tetration's recurrence follows by injectivity.
record InverseAbelChart : Set₁ where
  field
    Height : Set
    Value : Set
    successor : Height → Height
    exponential : Value → Value
    abel : Value → Height
    tetration : Height → Value
    abelStep :
      (w : Value) →
      abel (exponential w) ≡ successor (abel w)
    abelTetration :
      (h : Height) → abel (tetration h) ≡ h
    tetrationAbel :
      (w : Value) → tetration (abel w) ≡ w

open InverseAbelChart public

tetrationStepFromInverseAbel :
  (C : InverseAbelChart) →
  (h : InverseAbelChart.Height C) →
  InverseAbelChart.tetration C (InverseAbelChart.successor C h)
  ≡
  InverseAbelChart.exponential C (InverseAbelChart.tetration C h)
tetrationStepFromInverseAbel C h =
  trans
    (cong (InverseAbelChart.tetration C)
      (cong (InverseAbelChart.successor C)
        (symLocal (InverseAbelChart.abelTetration C h))))
    (trans
      (cong (InverseAbelChart.tetration C)
        (symLocal (InverseAbelChart.abelStep C
          (InverseAbelChart.tetration C h))))
      (InverseAbelChart.tetrationAbel C
        (InverseAbelChart.exponential C
          (InverseAbelChart.tetration C h))))
