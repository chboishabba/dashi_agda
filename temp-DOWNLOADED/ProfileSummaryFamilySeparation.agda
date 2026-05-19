module Ontology.Hecke.ProfileSummaryFamilySeparation where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Empty using (⊥)

open import DASHI.Physics.Closure.ShiftContractCollapseTime
  using (GeneratorCollapseClass)

open import Ontology.Hecke.DefectOrbitCollapseBridge
  using (primeImage)

open import Ontology.Hecke.FactorVecDefectOrbitSummaries
  using (profileSummaryFamily)

------------------------------------------------------------------------
-- Basic inequality

_≢_ : {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

------------------------------------------------------------------------
-- Core current-generator separation surface.
--
-- This asks the next honest question above the current exact Layer-1
-- pressure law:
--
--   does the full profileSummaryFamily already separate any current
--   generator pair through the existing representative prime-image bridge?
--
-- It does not claim that such a pair has been found yet.

CurrentProfileSummarySeparates : Set
CurrentProfileSummarySeparates =
  Σ GeneratorCollapseClass (λ c₁ →
  Σ GeneratorCollapseClass (λ c₂ →
    profileSummaryFamily (primeImage c₁)
      ≢
    profileSummaryFamily (primeImage c₂)))

------------------------------------------------------------------------
-- Honest collapse fallback.

CurrentProfileSummaryCollapses : Set
CurrentProfileSummaryCollapses =
  ∀ c₁ c₂ →
    profileSummaryFamily (primeImage c₁)
      ≡
    profileSummaryFamily (primeImage c₂)

------------------------------------------------------------------------
-- Thin packaged status surface, matching current repo style.

record ProfileSummaryLayer2 : Set₁ where
  field
    separates : Set
    collapses : Set

profileSummaryLayer2 : ProfileSummaryLayer2
profileSummaryLayer2 = record
  { separates = CurrentProfileSummarySeparates
  ; collapses = CurrentProfileSummaryCollapses
  }
