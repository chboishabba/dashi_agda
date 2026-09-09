module DASHI.Wikimedia.SensibLawZelphHFPrerequisiteBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Wikimedia.IdentifierExact as Id
import DASHI.Wikimedia.SensibLawStatementBundlePrerequisiteDAGExact as DAG

------------------------------------------------------------------------
-- ZELPH / HF BOUNDED SELECTOR BRIDGE
--
-- Source donors inspected on SensibLaw main d25cddf...:
--   src/ontology/wikidata_zelph_lane_plan.py
--     sl.wikidata_zelph_lane_plan.v0_1
--   src/ontology/wikidata_zelph_lane_proof.py
--     sl.wikidata_zelph_lane_proof.v0_1
--   src/policy/suite_normalized_artifact.py
--
-- Zelph/HF is an adjacent optional acquisition/execution surface.  It may
-- perform bounded selective reads that pay evidence-acquisition prerequisites.
-- It is not the semantic owner, proof oracle, source authority, edit authority,
-- or promotion authority.
------------------------------------------------------------------------

sensibLawZelphLanePlanReference : String
sensibLawZelphLanePlanReference =
  "SensibLaw src/ontology/wikidata_zelph_lane_plan.py @ d25cddf73540bdbb313777bbf566280f4e34313b; sl.wikidata_zelph_lane_plan.v0_1"

sensibLawZelphLaneProofReference : String
sensibLawZelphLaneProofReference =
  "SensibLaw src/ontology/wikidata_zelph_lane_proof.py @ d25cddf73540bdbb313777bbf566280f4e34313b; sl.wikidata_zelph_lane_proof.v0_1"

sensibLawHFTransportReference : String
sensibLawHFTransportReference =
  "SensibLaw build_zelph_hf_transport_normalized_artifact / zelph-hf-layout/v2 @ d25cddf73540bdbb313777bbf566280f4e34313b"

data ZelphHFOperation : Set where
  headerProbe
  selectedChunkRead
  nodeRouteSelection
  sparqlSubset
  transitivePropertyPaths
  partialLoading
  qualifierImport
  : ZelphHFOperation

record ZelphHFCapabilities : Set where
  constructor zelph-hf-capabilities
  field
    headerProbeSupported : Bool
    selectedChunkReadSupported : Bool
    nodeRouteIndexSupported : Bool
    sparqlSubsetSupported : Bool
    partialLoadingSupported : Bool
    qualifierImportReady : Bool
    propertyPathReady : Bool
    fullReasoningSafe : Bool
    hostedWDAcceptanceFinal : Bool
open ZelphHFCapabilities public

boundedLocalCapabilities : ZelphHFCapabilities
boundedLocalCapabilities =
  zelph-hf-capabilities true true true true true true true false false

boundedFullReasoningStillUnsupported :
  fullReasoningSafe boundedLocalCapabilities ≡ false
boundedFullReasoningStillUnsupported = refl

hostedAcceptanceStillPending :
  hostedWDAcceptanceFinal boundedLocalCapabilities ≡ false
hostedAcceptanceStillPending = refl

data SelectorKind : Set where routeSelector sectionSelector sparqlSelector : SelectorKind

record BoundedSelectorRequest : Set where
  constructor bounded-selector-request
  field
    selectorId : String
    selectorKind : SelectorKind
    qids : List Id.ItemId
    pids : List Id.PropertyId
    operations : List ZelphHFOperation
    manifestReference : String
    transportReference : String
    prerequisite : DAG.BundleObligation
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    reviewFirst : Bool
    reviewFirstIsTrue : reviewFirst ≡ true
    createsSemanticProof : Bool
    createsSemanticProofIsFalse : createsSemanticProof ≡ false
    createsSourceAuthority : Bool
    createsSourceAuthorityIsFalse : createsSourceAuthority ≡ false
    createsEditAuthority : Bool
    createsEditAuthorityIsFalse : createsEditAuthority ≡ false
open BoundedSelectorRequest public

------------------------------------------------------------------------
-- Which prerequisite classes may use Zelph/HF as an acquisition producer?
-- This is deliberately narrow.  A selector may support same-carrier checking,
-- source acquisition and provenance discovery.  Qualifier-bearing source reads
-- may prepare evidence for a later qualifier-transport theorem, but they do not
-- pay the transport node themselves. Terminal semantics remain Think work;
-- rank treatment remains Review work.
------------------------------------------------------------------------

data ZelphHFCanAcquireFor : DAG.BundleObligation → Set where
  carrierAcquisition : ZelphHFCanAcquireFor DAG.sameCarrier
  sourceAcquisition : ZelphHFCanAcquireFor DAG.sourceSupport
  provenanceAcquisition : ZelphHFCanAcquireFor DAG.provenanceSupport

record ZelphHFPrerequisitePaymentCandidate
    (obligation : DAG.BundleObligation) : Set where
  constructor zelph-hf-prerequisite-payment-candidate
  field
    selector : BoundedSelectorRequest
    selectorTargetsObligation : prerequisite selector ≡ obligation
    permitted : ZelphHFCanAcquireFor obligation
    acquiredEvidenceReceiptReference : String
    paymentStillNeedsConsumerVerification : Bool
    paymentStillNeedsConsumerVerificationIsTrue :
      paymentStillNeedsConsumerVerification ≡ true
open ZelphHFPrerequisitePaymentCandidate public

------------------------------------------------------------------------
-- Exact Nat climate request: the current DAG says source support is first
-- missing.  Fetch only bounded evidence around Q10403939 and P5991/P14143.
------------------------------------------------------------------------

natClimateSourceSelector : BoundedSelectorRequest
natClimateSourceSelector =
  bounded-selector-request
    "sel:nat:q10403939:p5991-p14143:source-support"
    sparqlSelector
    ((Id.itemId "Q10403939") ∷ [])
    ((Id.propertyId "P5991") ∷ (Id.propertyId "P14143") ∷ [])
    (sparqlSubset ∷ nodeRouteSelection ∷ partialLoading ∷ [])
    "zelph-hf-layout/v2 bounded/selective manifest; hosted manifest acceptance remains pending alignment"
    sensibLawHFTransportReference
    DAG.sourceSupport
    true refl
    true refl
    false refl
    false refl
    false refl

natClimateSourcePaymentCandidate :
  ZelphHFPrerequisitePaymentCandidate DAG.sourceSupport
natClimateSourcePaymentCandidate =
  zelph-hf-prerequisite-payment-candidate
    natClimateSourceSelector
    refl
    sourceAcquisition
    "bounded selected QID/PID reads may produce a source-support evidence receipt candidate"
    true refl

natSelectorTargetsCurrentFirstMissing :
  prerequisite natClimateSourceSelector
  ≡ DAG.obligationForResidual (DAG.firstResidual DAG.natCurrentCut)
natSelectorTargetsCurrentFirstMissing = refl

natSelectorIsCandidateOnly : candidateOnly natClimateSourceSelector ≡ true
natSelectorIsCandidateOnly = refl

natSelectorDoesNotCreateSemanticProof :
  createsSemanticProof natClimateSourceSelector ≡ false
natSelectorDoesNotCreateSemanticProof = refl

------------------------------------------------------------------------
-- A source-support selector may deliberately retain qualifier-bearing fields.
-- This prepares the later transport proof while remaining payment for the
-- current source-support acquisition node only.
------------------------------------------------------------------------

natQualifierBearingSourceSelector : BoundedSelectorRequest
natQualifierBearingSourceSelector =
  bounded-selector-request
    "sel:nat:q10403939:qualifier-bearing-source-support"
    routeSelector
    ((Id.itemId "Q10403939") ∷ [])
    ((Id.propertyId "P459") ∷ (Id.propertyId "P3831") ∷
     (Id.propertyId "P518") ∷ (Id.propertyId "P580") ∷
     (Id.propertyId "P582") ∷ [])
    (qualifierImport ∷ nodeRouteSelection ∷ selectedChunkRead ∷ [])
    "zelph-hf-layout/v2 qualifier-bearing route selector"
    sensibLawHFTransportReference
    DAG.sourceSupport
    true refl
    true refl
    false refl
    false refl
    false refl

qualifierBearingSelectorStillTargetsSourceSupport :
  prerequisite natQualifierBearingSourceSelector ≡ DAG.sourceSupport
qualifierBearingSelectorStillTargetsSourceSupport = refl

-- This selector is intentionally not a `ZelphHFPrerequisitePaymentCandidate`
-- for `qualifierTransport`: acquisition can prepare evidence, but the transport
-- node itself is paid only by an admitted theorem/proof route.

data ZelphHFProvesQualifierTransport : Set where
data ZelphHFProvesSemanticCorrespondence : Set where
data SelectedShardEqualsWholeWikidata : Set where
data HostedManifestPendingMeansEvidenceFalse : Set where
data ZelphCandidateBypassesReviewHold : Set where
data HFTransportCreatesSourceAuthority : Set where

zelphDoesNotProveQualifierTransport : ZelphHFProvesQualifierTransport → ⊥
zelphDoesNotProveQualifierTransport ()

zelphDoesNotProveSemanticCorrespondence :
  ZelphHFProvesSemanticCorrespondence → ⊥
zelphDoesNotProveSemanticCorrespondence ()

selectedShardDoesNotEqualWholeWikidata : SelectedShardEqualsWholeWikidata → ⊥
selectedShardDoesNotEqualWholeWikidata ()

pendingHostedManifestDoesNotMakeEvidenceFalse :
  HostedManifestPendingMeansEvidenceFalse → ⊥
pendingHostedManifestDoesNotMakeEvidenceFalse ()

zelphCandidateDoesNotBypassReviewHold : ZelphCandidateBypassesReviewHold → ⊥
zelphCandidateDoesNotBypassReviewHold ()

hfTransportDoesNotCreateSourceAuthority : HFTransportCreatesSourceAuthority → ⊥
hfTransportDoesNotCreateSourceAuthority ()

record ZelphHFPrerequisiteBoundary : Set where
  constructor zelph-hf-prerequisite-boundary
  field
    boundedSelectorsCanPayEvidenceAcquisitionCandidates : Bool
    terminalSemanticProofDelegatedToZelph : Bool
    qualifierTransportProofDelegatedToZelph : Bool
    fullReasoningSafeSupported : Bool
    candidateDiscoveryBypassesReviewHold : Bool
    selectedShardMeansWholeWikidata : Bool
    hostedManifestFinal : Bool
    transportCreatesAuthority : Bool

canonicalZelphHFPrerequisiteBoundary : ZelphHFPrerequisiteBoundary
canonicalZelphHFPrerequisiteBoundary =
  zelph-hf-prerequisite-boundary true false false false false false false false
