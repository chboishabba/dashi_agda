module DASHI.Core.ObservationLanguageRefinementExact where

------------------------------------------------------------------------
-- INTERNAL PRODUCER RECONCILIATION
--
-- Generalized from the exact structure of PR #549
-- `DASHI.Crypto.AttackerObservationLanguageRefinementExact`.
--
-- The theorem is domain-neutral: a base observation induces an equivalence;
-- adding an extra observation coordinate can only refine that equivalence, and
-- it refines strictly when the new coordinate separates two states that were
-- previously base-equivalent.
--
-- This is a DASHI finite theorem.  No external source is used as proof
-- authority for the exact construction.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

record ObservationLanguage : Set₁ where
  constructor observationLanguage
  field
    Hidden : Set
    Base : Set
    Extra : Set
    baseObservation : Hidden → Base
    extraObservation : Hidden → Extra

open ObservationLanguage public

BaseEquivalent :
  (language : ObservationLanguage) →
  Hidden language → Hidden language → Set
BaseEquivalent language left right =
  baseObservation language left ≡ baseObservation language right

ExtendedEquivalent :
  (language : ObservationLanguage) →
  Hidden language → Hidden language → Set
ExtendedEquivalent language left right =
  BaseEquivalent language left right
  × extraObservation language left ≡ extraObservation language right

extendedRefinesBase :
  ∀ {language : ObservationLanguage} {left right} →
  ExtendedEquivalent language left right →
  BaseEquivalent language left right
extendedRefinesBase extended = Data.Product.proj₁ extended

record LanguageSplitWitness
  (language : ObservationLanguage) : Set where
  constructor languageSplitWitness
  field
    left right : Hidden language
    baseSame : BaseEquivalent language left right
    extraDifferent :
      extraObservation language left ≡ extraObservation language right → ⊥

open LanguageSplitWitness public

splitRefutesExtendedEquivalence :
  ∀ {language : ObservationLanguage}
    (split : LanguageSplitWitness language) →
  ExtendedEquivalent language (left split) (right split) → ⊥
splitRefutesExtendedEquivalence split extended =
  extraDifferent split (Data.Product.proj₂ extended)

record StrictObservationRefinement
  (language : ObservationLanguage) : Set where
  constructor strictObservationRefinement
  field
    split : LanguageSplitWitness language

open StrictObservationRefinement public

strictRefinementWitnessesNewDistinction :
  ∀ {language : ObservationLanguage} →
  StrictObservationRefinement language →
  BaseEquivalent language
    (left (split _)) (right (split _))
strictRefinementWitnessesNewDistinction refinement =
  baseSame (split refinement)

strictRefinementRejectsOldCollision :
  ∀ {language : ObservationLanguage}
    (refinement : StrictObservationRefinement language) →
  ExtendedEquivalent language
    (left (split refinement)) (right (split refinement)) → ⊥
strictRefinementRejectsOldCollision refinement =
  splitRefutesExtendedEquivalence (split refinement)

------------------------------------------------------------------------
-- Boundary: refinement is informational, not automatically normative.
------------------------------------------------------------------------

record ObservationLanguageRefinementBoundary : Set where
  constructor observationLanguageRefinementBoundary
  field
    extendedEquivalenceAlwaysImpliesBaseEquivalence : Agda.Builtin.Bool.Bool
    baseEquivalenceAlwaysImpliesExtendedEquivalence : Agda.Builtin.Bool.Bool
    concreteSplitWitnessCanProveStrictRefinement : Agda.Builtin.Bool.Bool
    newObservationCoordinateAutomaticallyLegitimate : Agda.Builtin.Bool.Bool

open import Agda.Builtin.Bool using (Bool; false; true)

canonicalObservationLanguageRefinementBoundary :
  ObservationLanguageRefinementBoundary
canonicalObservationLanguageRefinementBoundary =
  observationLanguageRefinementBoundary true false true false
