module DASHI.Philosophy.PartialChartCategory where

open import Agda.Primitive using (Set₁)
open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- Partial charts form a category only after admissible-domain witnesses are
-- supplied. Failed translations remain outside the morphism type.

record PartialChartCategory : Set₁ where
  field
    Obj : Set

    Domain : Obj → Set

    Hom : Obj → Obj → Set

    admissible :
      {A B : Obj} →
      Hom A B →
      Domain A →
      Set

    id :
      {A : Obj} →
      Hom A A

    _∘_ :
      {A B C : Obj} →
      Hom B C →
      Hom A B →
      Hom A C

    idLeft :
      {A B : Obj} →
      (f : Hom A B) →
      id ∘ f ≡ f

    idRight :
      {A B : Obj} →
      (f : Hom A B) →
      f ∘ id ≡ f

    associative :
      {A B C D : Obj} →
      (h : Hom C D) →
      (g : Hom B C) →
      (f : Hom A B) →
      (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)

open PartialChartCategory public

record WitnessedInverse
       (C : PartialChartCategory)
       {A B : Obj C}
       (f : Hom C A B) : Set₁ where
  field
    inverse :
      Hom C B A

    inverseLeft :
      _∘_ C inverse f ≡ id C

    inverseRight :
      _∘_ C f inverse ≡ id C

open WitnessedInverse public

data TranslationFailure : Set where
  noOverlap : TranslationFailure
  authorityBlocked : TranslationFailure
  residualTooLarge : TranslationFailure
  unsafeTranslation : TranslationFailure
  unavailableWitness : TranslationFailure

record FailedTranslation
       (C : PartialChartCategory)
       (A B : Obj C) : Set₁ where
  field
    reason :
      TranslationFailure

    notPromotedToMorphism :
      Set

open FailedTranslation public
