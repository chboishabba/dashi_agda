{-# OPTIONS --safe #-}
module DASHI.Moonshine.AbelTetrationModularSymmetryExact where

-- Conditional modular S lift and exponential fixed-point obstruction.
-- Does not construct a Kneser Abel chart or an analytic modular j.

open import Agda.Primitive using (Set; Set₁)
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Moonshine.JInvariantTetrationAbelModularTransportExact as T

private
  variable
    A B : Set

cong : (f : A → B) → {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

trans : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

sym : {x y : A} → x ≡ y → y ≡ x
sym refl = refl

data ⊥ : Set where

record ModularInversionChart (S : T.AbelModularExpSystem) : Set₁ where
  field
    inversion : T.Coordinate S → T.Coordinate S
    inversionSquared :
      (z : T.Coordinate S) → inversion (inversion z) ≡ z
    inversionPreservesJ :
      (z : T.Coordinate S) →
      T.modularJ S (inversion z) ≡ T.modularJ S z
    section : T.Coordinate S → T.Point S
    abelSection :
      (z : T.Coordinate S) → T.abel S (section z) ≡ z
    sectionAbel :
      (w : T.Point S) → section (T.abel S w) ≡ w

open ModularInversionChart public

transportedInversion :
  (S : T.AbelModularExpSystem) →
  ModularInversionChart S → T.Point S → T.Point S
transportedInversion S C w =
  section C (inversion C (T.abel S w))

abelAfterTransportedInversion :
  (S : T.AbelModularExpSystem) →
  (C : ModularInversionChart S) →
  (w : T.Point S) →
  T.abel S (transportedInversion S C w) ≡
  inversion C (T.abel S w)
abelAfterTransportedInversion S C w =
  abelSection C (inversion C (T.abel S w))

transportedInversionSquared :
  (S : T.AbelModularExpSystem) →
  (C : ModularInversionChart S) →
  (w : T.Point S) →
  transportedInversion S C (transportedInversion S C w) ≡ w
transportedInversionSquared S C w =
  trans
    (cong (section C)
      (cong (inversion C) (abelAfterTransportedInversion S C w)))
    (trans
      (cong (section C) (inversionSquared C (T.abel S w)))
      (sectionAbel C w))

transportedJInvariantUnderInversion :
  (S : T.AbelModularExpSystem) →
  (C : ModularInversionChart S) →
  (w : T.Point S) →
  T.transportedJ S (transportedInversion S C w) ≡
  T.transportedJ S w
transportedJInvariantUnderInversion S C w =
  trans
    (cong (T.modularJ S) (abelAfterTransportedInversion S C w))
    (inversionPreservesJ C (T.abel S w))

record FixedPointFreeTranslation (S : T.AbelModularExpSystem) : Set₁ where
  field
    noTranslationFixedPoint :
      (z : T.Coordinate S) →
      T.translate S z ≡ z → ⊥

open FixedPointFreeTranslation public

exponentialHasNoFixedPointInAbelChart :
  (S : T.AbelModularExpSystem) →
  (F : FixedPointFreeTranslation S) →
  (w : T.Point S) →
  T.exponential S w ≡ w → ⊥
exponentialHasNoFixedPointInAbelChart S F w fixed =
  noTranslationFixedPoint F (T.abel S w)
    (trans
      (sym (T.abelExponentialLaw S w))
      (cong (T.abel S) fixed))
