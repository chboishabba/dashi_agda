module Ontology.Hecke.CurrentSaturatedContractiveCountLayer2Invariant where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Empty using (⊥)

open import Ontology.Hecke.ContractiveCountLayer2Invariant
  using (contractiveCountFamily)
open import Ontology.Hecke.CurrentSaturatedForcedStableCollapse
  using
    ( CurrentSaturatedGenerator
    ; saturatedGeneratorClass
    )
open import Ontology.Hecke.DefectOrbitCollapseBridge
  using (primeImage)

------------------------------------------------------------------------
-- Basic inequality

_≢_ : {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

------------------------------------------------------------------------
-- Current saturated-scope specialization.

currentSaturated-contractiveCount-separates : Set
currentSaturated-contractiveCount-separates =
  Σ CurrentSaturatedGenerator (λ c₁ →
  Σ CurrentSaturatedGenerator (λ c₂ →
    contractiveCountFamily (primeImage (saturatedGeneratorClass c₁))
      ≢
    contractiveCountFamily (primeImage (saturatedGeneratorClass c₂))))

currentSaturated-contractiveCount-collapses : Set
currentSaturated-contractiveCount-collapses =
  ∀ c₁ c₂ →
    contractiveCountFamily (primeImage (saturatedGeneratorClass c₁))
      ≡
    contractiveCountFamily (primeImage (saturatedGeneratorClass c₂))

record CurrentSaturatedContractiveCountLayer2 : Set₁ where
  field
    separates : Set
    collapses : Set

currentSaturatedContractiveCountLayer2 :
  CurrentSaturatedContractiveCountLayer2
currentSaturatedContractiveCountLayer2 = record
  { separates = currentSaturated-contractiveCount-separates
  ; collapses = currentSaturated-contractiveCount-collapses
  }
