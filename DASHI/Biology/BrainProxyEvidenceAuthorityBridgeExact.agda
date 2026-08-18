module DASHI.Biology.BrainProxyEvidenceAuthorityBridgeExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Algebra.DisagreementFourViewBoundary as Four
import DASHI.Biology.FMRIConnectomeProxyGovernance as FMRI
import DASHI.Biology.BrainDNABodyMemoryBridge as BrainDNA
import DASHI.Core.EvidenceObligationAuthoritySeparationExact as Governed
import DASHI.Promotion.AuthorityGateCore as Authority

------------------------------------------------------------------------
-- Brain / body-memory proxy instantiation.
--
-- The existing repo already distinguishes BOLD measurement, connectome graph,
-- functional-connectivity, BrainDNA representation, and reverse inference from
-- hidden-state, diagnostic, therapeutic, or clinical authority.  A positive
-- proxy observation can therefore inhabit the evidence coordinate while the
-- obligation coordinate remains open and the existing clinical authority gate
-- stays fail-closed.
------------------------------------------------------------------------

proxyObservationSupportedOnly : Governed.GovernedClaimState
proxyObservationSupportedOnly =
  Governed.closedGovernedClaimState
    (Four.assess true false)
    Governed.obligationsOpen
    Authority.clinicalAuthority
    "brain proxy observation to clinical authority"

proxySupportDoesNotPromoteHiddenState :
  Governed.localPromotion proxyObservationSupportedOnly ≡ false
proxySupportDoesNotPromoteHiddenState =
  Governed.localPromotionIsFalse proxyObservationSupportedOnly

clinicalProxyAuthorityStillRejected :
  FMRI.AdmissibleFMRIConnectomeProxyRoute FMRI.clinicalAuthorityRoute →
  FMRI.Never
clinicalProxyAuthorityStillRejected = FMRI.clinicalAuthorityRouteRejected

brainDNATraumaProofStillRejected :
  BrainDNA.AdmissibleBrainDNABodyMemoryRoute BrainDNA.traumaProofRoute →
  BrainDNA.Never
brainDNATraumaProofStillRejected = BrainDNA.traumaProofRejected

record BrainProxyEvidenceAuthorityBoundary : Set where
  field
    measurementProxyDistinctFromHiddenState : Bool
    connectomeProxyDistinctFromDiagnosis : Bool
    representationDistinctFromTraumaProof : Bool
    proxySupportEqualsClinicalAuthorityClaimed : Bool
    canonicalAuthorityGateCoreReused : Bool

canonicalBrainProxyEvidenceAuthorityBoundary :
  BrainProxyEvidenceAuthorityBoundary
canonicalBrainProxyEvidenceAuthorityBoundary = record
  { measurementProxyDistinctFromHiddenState = true
  ; connectomeProxyDistinctFromDiagnosis = true
  ; representationDistinctFromTraumaProof = true
  ; proxySupportEqualsClinicalAuthorityClaimed = false
  ; canonicalAuthorityGateCoreReused = true
  }
