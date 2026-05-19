module Ontology.Hecke.CurrentSaturatedProfileSummaryFamilySeparation where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Empty using (⊥)

open import Ontology.Hecke.CurrentSaturatedForcedStableCollapse
  using
    ( CurrentSaturatedGenerator
    ; saturatedGeneratorClass
    )

open import Ontology.Hecke.DefectOrbitCollapseBridge
  using (primeImage)

open import Ontology.Hecke.FactorVecDefectOrbitSummaries
  using (profileSummaryFamily)

------------------------------------------------------------------------
-- Basic inequality

_≢_ : {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

------------------------------------------------------------------------
-- Current saturated-scope specialization.
--
-- This is the direct analogue of the existing current saturated separator
-- modules, but lifted to the full profileSummaryFamily surface instead of
-- the already-collapsed p2-only orbit-summary or scalar forced-stable
-- counts.
--
-- The question is:
--
--   does the full prime-indexed profileSummaryFamily distinguish any pair
--   of current saturated generators once each class is mapped through the
--   canonical saturated generator embedding and then through primeImage?

currentSaturated-profileSummaryFamily-separates : Set
currentSaturated-profileSummaryFamily-separates =
  Σ CurrentSaturatedGenerator (λ c₁ →
  Σ CurrentSaturatedGenerator (λ c₂ →
    profileSummaryFamily (primeImage (saturatedGeneratorClass c₁))
      ≢
    profileSummaryFamily (primeImage (saturatedGeneratorClass c₂))))

------------------------------------------------------------------------
-- Honest collapse fallback on the current saturated branch.

currentSaturated-profileSummaryFamily-collapses : Set
currentSaturated-profileSummaryFamily-collapses =
  ∀ c₁ c₂ →
    profileSummaryFamily (primeImage (saturatedGeneratorClass c₁))
      ≡
    profileSummaryFamily (primeImage (saturatedGeneratorClass c₂)

      )

------------------------------------------------------------------------
-- Small packaged theorem surface.

record CurrentSaturatedProfileSummaryLayer2 : Set₁ where
  field
    separates : Set
    collapses : Set

currentSaturatedProfileSummaryLayer2 :
  CurrentSaturatedProfileSummaryLayer2
currentSaturatedProfileSummaryLayer2 = record
  { separates = currentSaturated-profileSummaryFamily-separates
  ; collapses = currentSaturated-profileSummaryFamily-collapses
  }
