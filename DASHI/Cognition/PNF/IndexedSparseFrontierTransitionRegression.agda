module DASHI.Cognition.PNF.IndexedSparseFrontierTransitionRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Unit using (⊤; tt)

open import DASHI.Cognition.PNF.IndexedSparseFrontierTransitionExact

LegacyRetention IndexedRetention LegacyCandidate IndexedCandidate : ⊤ → ⊤ → Set
LegacyRetention _ _ = ⊤
IndexedRetention _ _ = ⊤
LegacyCandidate _ _ = ⊤
IndexedCandidate _ _ = ⊤

transition : IndexedSparseFrontierTransition
transition = record
  { RetentionDemand = ⊤
  ; RetentionProfile = ⊤
  ; CandidateDemand = ⊤
  ; CandidateProfile = ⊤
  ; legacyRetention = LegacyRetention
  ; indexedRetention = IndexedRetention
  ; retentionExact = λ _ _ → refl
  ; legacyCandidate = LegacyCandidate
  ; indexedCandidate = IndexedCandidate
  ; candidateExact = λ _ _ → refl
  ; legacyRetentionExposure = cartesianTransitionExposure 11 23
  ; indexedRetentionExposure = indexedTransitionExposure 11 23 19 69 31
  ; legacyCandidateExposure = cartesianTransitionExposure 11 23
  ; indexedCandidateExposure = indexedTransitionExposure 11 23 27 92 41
  }

factorisation : IndexedExposureFactorisation transition
factorisation = indexedExposureFactorisation refl refl

retentionParity :
  legacyRetention transition tt tt
    ≡ indexedRetention transition tt tt
retentionParity = sameRetentionRelation transition tt tt

candidateParity :
  legacyCandidate transition tt tt
    ≡ indexedCandidate transition tt tt
candidateParity = sameCandidateRelation transition tt tt
