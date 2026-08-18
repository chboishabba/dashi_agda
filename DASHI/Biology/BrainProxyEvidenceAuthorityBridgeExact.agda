module DASHI.Biology.BrainProxyEvidenceAuthorityBridgeExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Algebra.DisagreementFourViewBoundary as Four
import DASHI.Biology.FMRIConnectomeProxyGovernance as FMRI
import DASHI.Biology.BrainDNABodyMemoryBridge as BrainDNA
import DASHI.Core.EvidenceObligationAuthoritySeparationExact as Governed

------------------------------------------------------------------------
-- Brain / body-memory proxy instantiation.
--
-- The existing repo already distinguishes BOLD measurement, connectome graph,
-- functional-connectivity, BrainDNA representation, and reverse inference from
-- hidden-state, diagnostic, therapeutic, or clinical authority.  A positive
-- proxy observation can therefore inhabit the evidence coordinate while the
-- obligation and authority coordinates remain open/denied.
------------------------------------------------------------------------

proxyObservationSupportedOnly : Governed.GovernedClaimState
proxyObservationSupportedOnly =
  Governed.governedClaimState
    (Four.assess true false)
    Governed.obligationsOpen
    Governed.authorityDenied

proxySupportDoesNotPromoteHiddenState :
  Governed.promotionGate proxyObservationSupportedOnly ≡ false
proxySupportDoesNotPromoteHiddenState = refl

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
    genericGovernedClaimStateReused : Bool

canonicalBrainProxyEvidenceAuthorityBoundary :
  BrainProxyEvidenceAuthorityBoundary
canonicalBrainProxyEvidenceAuthorityBoundary = record
  { measurementProxyDistinctFromHiddenState = true
  ; connectomeProxyDistinctFromDiagnosis = true
  ; representationDistinctFromTraumaProof = true
  ; proxySupportEqualsClinicalAuthorityClaimed = false
  ; genericGovernedClaimStateReused = true
  }
