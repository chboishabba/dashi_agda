module Ontology.Hecke.ContractiveCountLayer2Invariant where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Empty using (⊥)

open import MonsterOntos using
  ( p2
  ; p3
  ; p5
  ; p7
  ; p11
  ; p13
  ; p17
  ; p19
  ; p23
  ; p29
  ; p31
  ; p41
  ; p47
  ; p59
  ; p71
  )
open import Ontology.GodelLattice using (FactorVec)
open import Ontology.GodelLattice renaming (Vec15 to Vec15' ; v15 to mkVec15)

open import DASHI.Physics.Closure.ShiftContractCollapseTime
  using (GeneratorCollapseClass)

open import Ontology.Hecke.DefectOrbitCollapseBridge
  using (primeImage)
open import Ontology.Hecke.FactorVecDefectOrbitSummaries as FOS
  using
    ( DefectOrbitSummary
    ; profileSummaryAt
    )

------------------------------------------------------------------------
-- Basic inequality

_≢_ : {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

------------------------------------------------------------------------
-- Lane-wise singleton projection of the full profile family.

contractiveCountFamily : FactorVec → Vec15' Nat
contractiveCountFamily v =
  mkVec15
    (FOS.DefectOrbitSummary.contractiveCount (profileSummaryAt p2  v))
    (FOS.DefectOrbitSummary.contractiveCount (profileSummaryAt p3  v))
    (FOS.DefectOrbitSummary.contractiveCount (profileSummaryAt p5  v))
    (FOS.DefectOrbitSummary.contractiveCount (profileSummaryAt p7  v))
    (FOS.DefectOrbitSummary.contractiveCount (profileSummaryAt p11 v))
    (FOS.DefectOrbitSummary.contractiveCount (profileSummaryAt p13 v))
    (FOS.DefectOrbitSummary.contractiveCount (profileSummaryAt p17 v))
    (FOS.DefectOrbitSummary.contractiveCount (profileSummaryAt p19 v))
    (FOS.DefectOrbitSummary.contractiveCount (profileSummaryAt p23 v))
    (FOS.DefectOrbitSummary.contractiveCount (profileSummaryAt p29 v))
    (FOS.DefectOrbitSummary.contractiveCount (profileSummaryAt p31 v))
    (FOS.DefectOrbitSummary.contractiveCount (profileSummaryAt p41 v))
    (FOS.DefectOrbitSummary.contractiveCount (profileSummaryAt p47 v))
    (FOS.DefectOrbitSummary.contractiveCount (profileSummaryAt p59 v))
    (FOS.DefectOrbitSummary.contractiveCount (profileSummaryAt p71 v))

sameContractiveCountFamily : FactorVec → FactorVec → Set
sameContractiveCountFamily x y =
  contractiveCountFamily x ≡ contractiveCountFamily y

------------------------------------------------------------------------
-- Current-generator Layer-2 theorem surfaces.

CurrentContractiveCountSeparates : Set
CurrentContractiveCountSeparates =
  Σ GeneratorCollapseClass (λ c₁ →
  Σ GeneratorCollapseClass (λ c₂ →
    contractiveCountFamily (primeImage c₁)
      ≢
    contractiveCountFamily (primeImage c₂)))

CurrentContractiveCountCollapses : Set
CurrentContractiveCountCollapses =
  ∀ c₁ c₂ →
    contractiveCountFamily (primeImage c₁)
      ≡
    contractiveCountFamily (primeImage c₂)

record ContractiveCountLayer2 : Set₁ where
  field
    separates : Set
    collapses : Set

contractiveCountLayer2 : ContractiveCountLayer2
contractiveCountLayer2 = record
  { separates = CurrentContractiveCountSeparates
  ; collapses = CurrentContractiveCountCollapses
  }
