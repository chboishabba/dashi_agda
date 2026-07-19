module DASHI.Biology.Cannabis.TerpeneClusterPromotionBoundaryTests where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)
open import DASHI.Biology.Cannabis.TerpeneClusterPromotionBoundary
open import DASHI.Biology.Cannabis.TerpeneCommentInterpretation

data Sample : Set where sample₀ : Sample
data Terpene : Set where terpene₀ : Terpene
data Effect : Set where effect₀ : Effect

profile₀ : TerpeneProfile Terpene
profile₀ = record { abundance = λ _ → 0 }

chemical₀ : ChemicalClusterReceipt Sample Terpene
chemical₀ = record
  { profile  = λ _ → profile₀
  ; classify = λ _ → cluster₂
  }

association₀ : AssociationReceipt Sample Effect
association₀ = record
  { reportedAssociation = λ _ _ → ⊤ }

protocol₀ : ValidatedProtocol Sample ⊤
protocol₀ = record
  { protocol      = λ _ → tt
  ; validProtocol = λ _ → ⊤
  ; validation    = λ _ → tt
  }

exposure₀ : ExposureLink Sample ⊤
exposure₀ = record
  { exposure             = λ _ → tt
  ; exposureMatchesClaim = λ _ → ⊤
  ; matchWitness         = λ _ → tt
  }

causal₀ : CausalStudyReceipt Sample Effect ⊤ ⊤ ⊤ ⊤ ⊤ ⊤ ⊤
causal₀ = record
  { assignedDose         = λ _ → tt
  ; assignedRoute        = λ _ → tt
  ; administration       = λ _ → tt
  ; comparator           = λ _ → tt
  ; measuredOutcome      = λ _ → tt
  ; effectInterpretation = λ _ → effect₀
  ; protocolReceipt      = protocol₀
  ; exposureReceipt      = exposure₀
  }

Evidence : Set₁
Evidence = ClusterEffectEvidence Sample Terpene Effect ⊤ ⊤ ⊤ ⊤ ⊤ ⊤ ⊤
  ⊤ ⊤ ⊤ ⊤ ⊤ ⊤

chemicalEvidence₀ : Evidence
chemicalEvidence₀ = chemical-only chemical₀

associationEvidence₀ : Evidence
associationEvidence₀ = association-only chemical₀ association₀

causalEvidence₀ : Evidence
causalEvidence₀ = causal-study-supported chemical₀ causal₀

concrete-chemical-stage-is-closed :
  status chemicalEvidence₀ ≡ chemical-established
concrete-chemical-stage-is-closed = refl

concrete-association-is-candidate-only :
  status associationEvidence₀ ≡ association-candidate
concrete-association-is-candidate-only = refl

concrete-causal-study-stops-before-replication :
  status causalEvidence₀ ≡ causal-study-bounded
concrete-causal-study-stops-before-replication = refl

commentary-does-not-promote :
  authority correlation-warning ≡ framing-only
commentary-does-not-promote = refl

causal-denial-needs-mechanism :
  obligation terpene-causality-denial ≡ mechanistic-experiment-required
causal-denial-needs-mechanism = refl
