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
-- Core separation target on the current generator domain

CurrentProfileSummarySeparates : Set
CurrentProfileSummarySeparates =
  Σ GeneratorCollapseClass (λ c₁ →
  Σ GeneratorCollapseClass (λ c₂ →
    profileSummaryFamily (primeImage c₁)
      ≢
    profileSummaryFamily (primeImage c₂)))

------------------------------------------------------------------------
-- Collapse fallback (honest boundary)

CurrentProfileSummaryCollapses : Set
CurrentProfileSummaryCollapses =
  ∀ c₁ c₂ →
    profileSummaryFamily (primeImage c₁)
      ≡
    profileSummaryFamily (primeImage c₂)

------------------------------------------------------------------------
-- Layer-2 style packaging

record ProfileSummaryLayer2 : Set₁ where
  field
    separates : Set
    collapses : Set

profileSummaryLayer2 : ProfileSummaryLayer2
profileSummaryLayer2 = record
  { separates = CurrentProfileSummarySeparates
  ; collapses = CurrentProfileSummaryCollapses
  }
