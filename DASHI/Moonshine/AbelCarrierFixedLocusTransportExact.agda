{-# OPTIONS --safe #-}
module DASHI.Moonshine.AbelCarrierFixedLocusTransportExact where

-- Arbitrary carriers: no ring, field, characteristic or Archimedean law.
-- An Abel semiconjugacy sends E-fixed points to T-fixed points.
-- The inverse-image formulation remains meaningful when T has fixed points.

open import Agda.Primitive using (Set; Set₁)
open import Agda.Builtin.Equality using (_≡_; refl)

private
  variable
    A B : Set

cong : (f : A → B) → {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

trans : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

sym : {x y : A} → x ≡ y → y ≡ x
sym refl = refl

record AbelCarrier : Set₁ where
  field
    Fine : Set
    Coordinate : Set
    Base : Set
    step : Fine → Fine
    translate : Coordinate → Coordinate
    abel : Fine → Coordinate
    quotient : Coordinate → Base
    abelCommutes : (x : Fine) →
      abel (step x) ≡ translate (abel x)
    quotientInvariant : (z : Coordinate) →
      quotient (translate z) ≡ quotient z

open AbelCarrier public

Fixed : {A : Set} → (A → A) → A → Set
Fixed f x = f x ≡ x

fixedFineMapsToFixedCoordinate :
  (C : AbelCarrier) → (x : Fine C) →
  Fixed (step C) x → Fixed (translate C) (abel C x)
fixedFineMapsToFixedCoordinate C x fixed =
  trans
    (sym (abelCommutes C x))
    (cong (abel C) fixed)

observed : (C : AbelCarrier) → Fine C → Base C
observed C x = quotient C (abel C x)

quotientStepInvariant :
  (C : AbelCarrier) → (x : Fine C) →
  observed C (step C x) ≡ observed C x
quotientStepInvariant C x =
  trans
    (cong (quotient C) (abelCommutes C x))
    (quotientInvariant C (abel C x))

record Observer (C : AbelCarrier) : Set₁ where
  field
    Coarse : Set
    readout : Base C → Coarse

open Observer public

coarseObserved : (C : AbelCarrier) →
  (O : Observer C) → Fine C → Coarse O
coarseObserved C O x = readout O (observed C x)

coarseStepInvariant :
  (C : AbelCarrier) → (O : Observer C) → (x : Fine C) →
  coarseObserved C O (step C x) ≡ coarseObserved C O x
coarseStepInvariant C O x =
  cong (readout O) (quotientStepInvariant C x)

Fibre : (C : AbelCarrier) → (b : Base C) → Fine C → Set
Fibre C b x = observed C x ≡ b

stepPreservesFibre :
  (C : AbelCarrier) → (b : Base C) → (x : Fine C) →
  Fibre C b x → Fibre C b (step C x)
stepPreservesFibre C b x witness =
  trans (quotientStepInvariant C x) witness

data Empty : Set where

record FixedPointFree (C : AbelCarrier) : Set₁ where
  field
    contradiction : (z : Coordinate C) →
      Fixed (translate C) z → Empty

open FixedPointFree public

fineCannotBeFixedWhenTranslationFree :
  (C : AbelCarrier) → (F : FixedPointFree C) →
  (x : Fine C) → Fixed (step C) x → Empty
fineCannotBeFixedWhenTranslationFree C F x fixed =
  contradiction F (abel C x)
    (fixedFineMapsToFixedCoordinate C x fixed)

-- A quotient invariant does not force a fine coordinate to be invariant.
-- That would contradict translation fixed-point freedom.

record CoordinateDescent (C : AbelCarrier) : Set₁ where
  field
    decode : Base C → Coordinate C
    factors : (x : Fine C) →
      abel C x ≡ decode (observed C x)

open CoordinateDescent public

coordinateDescentForcesTranslationFixed :
  (C : AbelCarrier) → (D : CoordinateDescent C) →
  (x : Fine C) → Fixed (translate C) (abel C x)
coordinateDescentForcesTranslationFixed C D x =
  trans
    (sym (abelCommutes C x))
    (trans
      (factors D (step C x))
      (trans
        (cong (decode D) (quotientStepInvariant C x))
        (sym (factors D x))))

coordinateCannotDescendWhenTranslationFree :
  (C : AbelCarrier) → (F : FixedPointFree C) →
  (D : CoordinateDescent C) → (x : Fine C) → Empty
coordinateCannotDescendWhenTranslationFree C F D x =
  contradiction F (abel C x)
    (coordinateDescentForcesTranslationFixed C D x)
