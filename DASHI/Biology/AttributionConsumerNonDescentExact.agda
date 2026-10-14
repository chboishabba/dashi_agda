module DASHI.Biology.AttributionConsumerNonDescentExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Core.Prelude using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.ConsumerDescentMinimalObserverExact as Consumer
import DASHI.Biology.AutismTranscriptHighAlphaCrossPollinationExact as HighAlpha

------------------------------------------------------------------------
-- ATTRIBUTION AS A CONSUMER-DESCENT PROBLEM
--
-- A source/provenance coordinate can be perfectly preserved while remaining
-- insufficient for a claim-sensitive consumer.  This is the formal version of
-- the repo-wide attribution rule:
--
--   source identity != claim content != result status != causal authority
--                   != diagnosis != DASHI synthesis.
--
-- The concrete fixture deliberately uses two outcomes reported from the same
-- admitted Wan-2024 FMT trial.  The source observation is identical, while an
-- endpoint-sensitive consumer distinguishes the primary SRS-2 null from the
-- secondary Vineland socialisation signal.  Nothing here promotes either
-- endpoint beyond the bounded reading already owned by HighAlpha.
------------------------------------------------------------------------

data FMTEndpointMeaning : Set where
  primarySRSBetweenGroupNull : FMTEndpointMeaning
  secondaryVinelandSocialisationSignal : FMTEndpointMeaning

record AttributedFMTEndpointState : Set where
  constructor attributed-fmt-endpoint-state
  field
    sourceAdmission :
      HighAlpha.AdmittedHighAlphaSource
        HighAlpha.fmtTrialOutcome
        HighAlpha.wan2024FMTSource
    endpointMeaning : FMTEndpointMeaning

open AttributedFMTEndpointState public

wanPrimaryEndpointState : AttributedFMTEndpointState
wanPrimaryEndpointState =
  attributed-fmt-endpoint-state
    HighAlpha.wan2024PaysFMTTrialOutcome
    primarySRSBetweenGroupNull

wanSecondaryEndpointState : AttributedFMTEndpointState
wanSecondaryEndpointState =
  attributed-fmt-endpoint-state
    HighAlpha.wan2024PaysFMTTrialOutcome
    secondaryVinelandSocialisationSignal

provenanceObserve : AttributedFMTEndpointState → Source.AttributedSource
provenanceObserve _ = HighAlpha.wan2024FMTSource

endpointConsumer : AttributedFMTEndpointState → FMTEndpointMeaning
endpointConsumer = endpointMeaning

wanEndpointSourceOnlyNonDescent :
  Consumer.ConsumerNonDescentWitness provenanceObserve endpointConsumer
wanEndpointSourceOnlyNonDescent =
  Consumer.consumerNonDescentWitness
    wanPrimaryEndpointState
    wanSecondaryEndpointState
    refl
    (λ ())

sourceIdentityAloneCannotRecoverEndpointMeaning :
  Consumer.FactorsThrough provenanceObserve endpointConsumer → ⊥
sourceIdentityAloneCannotRecoverEndpointMeaning =
  Consumer.nonDescentWitnessBlocksFactorization wanEndpointSourceOnlyNonDescent

------------------------------------------------------------------------
-- PROMOTION FIREWALLS
--
-- These are separate from the consumer collision.  The collision proves that
-- provenance alone is not sufficient for endpoint meaning; the empty
-- permissions make explicit that provenance is also not a truth/authority
-- constructor and that DASHI synthesis may not be back-attributed to a source.
------------------------------------------------------------------------

data SourceIdentityImportsTruthPermission : Set where
data SourceIdentityImportsCausalAuthorityPermission : Set where
data SourceIdentityImportsDiagnosisPermission : Set where
data BackAttributeDASHISynthesisToSourcePermission : Set where

sourceIdentityDoesNotImportTruth :
  SourceIdentityImportsTruthPermission → ⊥
sourceIdentityDoesNotImportTruth ()

sourceIdentityDoesNotImportCausalAuthority :
  SourceIdentityImportsCausalAuthorityPermission → ⊥
sourceIdentityDoesNotImportCausalAuthority ()

sourceIdentityDoesNotImportDiagnosis :
  SourceIdentityImportsDiagnosisPermission → ⊥
sourceIdentityDoesNotImportDiagnosis ()

dashISynthesisRemainsSeparateOwner :
  BackAttributeDASHISynthesisToSourcePermission → ⊥
dashISynthesisRemainsSeparateOwner ()

record AttributionConsumerBoundary : Set where
  constructor attribution-consumer-boundary
  field
    sourceProvenanceRetained : Bool
    sourceProvenanceRetainedIsTrue : sourceProvenanceRetained ≡ true
    sourceIdentityDeterminesEndpointMeaning : Bool
    sourceIdentityDeterminesEndpointMeaningIsFalse :
      sourceIdentityDeterminesEndpointMeaning ≡ false
    sourceIdentityImportsTruthAuthority : Bool
    sourceIdentityImportsTruthAuthorityIsFalse :
      sourceIdentityImportsTruthAuthority ≡ false
    sourceIdentityImportsCausalAuthority : Bool
    sourceIdentityImportsCausalAuthorityIsFalse :
      sourceIdentityImportsCausalAuthority ≡ false
    sourceIdentityImportsDiagnosis : Bool
    sourceIdentityImportsDiagnosisIsFalse :
      sourceIdentityImportsDiagnosis ≡ false
    dashiSynthesisBackAttributedToSource : Bool
    dashiSynthesisBackAttributedToSourceIsFalse :
      dashiSynthesisBackAttributedToSource ≡ false

open AttributionConsumerBoundary public

canonicalAttributionConsumerBoundary : AttributionConsumerBoundary
canonicalAttributionConsumerBoundary =
  attribution-consumer-boundary
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
