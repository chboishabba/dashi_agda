module DASHI.Foundations.FibreConstantObservableExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Saunders Mac Lane,
-- "Categories for the Working Mathematician", 2nd ed., Springer, 1998.
-- DOI: 10.1007/978-1-4757-4721-8.
--
-- DASHI CONTRIBUTION
--
-- Extract the exact quotient discipline used independently by the C9 -> C3
-- character pullback and by fine -> coarse Hecke/Brandt projections.
--
-- A coarse observable pulls back to a fine observable that is constant on
-- quotient fibres.  Conversely, on a sectioned quotient, every fibre-constant
-- fine observable is pointwise equal to the pullback of its values on the
-- chosen representatives.  None of this identifies the fine and coarse
-- carriers; nontrivial fibres remain allowed and visible.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

record SectionedQuotient (Fine Coarse : Set) : Set₁ where
  field
    project : Fine → Coarse
    representative : Coarse → Fine
    section : (c : Coarse) → project (representative c) ≡ c

open SectionedQuotient public

FibreConstant :
  ∀ {Fine Coarse Value : Set} →
  (Fine → Coarse) → (Fine → Value) → Set
FibreConstant project observable =
  ∀ x y → project x ≡ project y → observable x ≡ observable y

pullback :
  ∀ {Fine Coarse Value : Set} →
  (Fine → Coarse) → (Coarse → Value) → Fine → Value
pullback project coarseObservable x = coarseObservable (project x)

pullbackIsFibreConstant :
  ∀ {Fine Coarse Value : Set}
    (project : Fine → Coarse)
    (coarseObservable : Coarse → Value) →
  FibreConstant project (pullback project coarseObservable)
pullbackIsFibreConstant project coarseObservable x y equality =
  cong coarseObservable equality

representativeObservable :
  ∀ {Fine Coarse Value : Set} →
  SectionedQuotient Fine Coarse →
  (Fine → Value) → Coarse → Value
representativeObservable quotient observable c =
  observable (representative quotient c)

fibreConstantObservableReconstructsFromRepresentatives :
  ∀ {Fine Coarse Value : Set}
    (quotient : SectionedQuotient Fine Coarse)
    (observable : Fine → Value) →
  FibreConstant (project quotient) observable →
  (x : Fine) →
  observable x
  ≡ pullback
      (project quotient)
      (representativeObservable quotient observable)
      x
fibreConstantObservableReconstructsFromRepresentatives
  quotient observable constantOnFibres x =
  constantOnFibres
    x
    (representative quotient (project quotient x))
    (sym (section quotient (project quotient x)))

coarseObservableRecoveredOnSection :
  ∀ {Fine Coarse Value : Set}
    (quotient : SectionedQuotient Fine Coarse)
    (coarseObservable : Coarse → Value)
    (c : Coarse) →
  pullback (project quotient) coarseObservable (representative quotient c)
  ≡ coarseObservable c
coarseObservableRecoveredOnSection quotient coarseObservable c =
  cong coarseObservable (section quotient c)

------------------------------------------------------------------------
-- Exact separation witness: a section does not make projection injective.
------------------------------------------------------------------------

record NontrivialFibre
    {Fine Coarse : Set}
    (quotient : SectionedQuotient Fine Coarse) : Set where
  field
    left right : Fine
    sameProjection : project quotient left ≡ project quotient right
    distinctFine : left ≡ right → ⊥

open NontrivialFibre public

nontrivialFibreBlocksProjectionInjectivity :
  ∀ {Fine Coarse : Set}
    {quotient : SectionedQuotient Fine Coarse} →
  NontrivialFibre quotient →
  ((x y : Fine) → project quotient x ≡ project quotient y → x ≡ y) →
  ⊥
nontrivialFibreBlocksProjectionInjectivity witness injective =
  distinctFine witness
    (injective
      (left witness)
      (right witness)
      (sameProjection witness))

record FibreConstantObservableBoundary : Set where
  field
    pullbackFibreConstancyConstructed : Bool
    pullbackFibreConstancyConstructedIsTrue :
      pullbackFibreConstancyConstructed ≡ true

    sectionedReconstructionConstructed : Bool
    sectionedReconstructionConstructedIsTrue :
      sectionedReconstructionConstructed ≡ true

    quotientPromotedToCarrierIdentity : Bool
    quotientPromotedToCarrierIdentityIsFalse :
      quotientPromotedToCarrierIdentity ≡ false

canonicalFibreConstantObservableBoundary : FibreConstantObservableBoundary
canonicalFibreConstantObservableBoundary = record
  { pullbackFibreConstancyConstructed = true
  ; pullbackFibreConstancyConstructedIsTrue = refl
  ; sectionedReconstructionConstructed = true
  ; sectionedReconstructionConstructedIsTrue = refl
  ; quotientPromotedToCarrierIdentity = false
  ; quotientPromotedToCarrierIdentityIsFalse = refl
  }
