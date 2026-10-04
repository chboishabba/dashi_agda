module DASHI.Core.GenderedNormApprovalRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.GenderedNormApprovalIndependenceExact as Norm
import DASHI.Core.GenderedNormApprovalSourceExact as Source

reward-does-not-entail-refusal-sanction :
  Norm.RelatabilityRewardAdequateForRefusalSanction → ⊥
reward-does-not-entail-refusal-sanction =
  Norm.relatabilityRewardDoesNotEntailRefusalSanction

likability-does-not-determine-respect :
  Norm.LikabilityAdequateForRespect → ⊥
likability-does-not-determine-respect =
  Norm.likabilityDoesNotDetermineRespect

likability-does-not-determine-loyalty :
  Norm.LikabilityAdequateForLoyalty → ⊥
likability-does-not-determine-loyalty =
  Norm.likabilityDoesNotDetermineLoyalty

fear-is-not-promoted-to-respect :
  Norm.fearAutomaticallyIdenticalToRespect
    Norm.canonicalGenderedNormApprovalBoundary ≡ false
fear-is-not-promoted-to-respect = refl

transcript-is-not-promoted-to-proof :
  Source.transcriptIsEmpiricalProof
    Source.canonicalSourceFormalisationBoundary ≡ false
transcript-is-not-promoted-to-proof = refl

external-validation-remains-required :
  Source.empiricalValidationStillRequired
    Source.canonicalSourceFormalisationBoundary ≡ true
external-validation-remains-required = refl
