module DASHI.Biology.AnimalexicStaticAnchorCandidateIdentityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- STATIC ANCHOR CANDIDATE DISCOVERY -> EXPLICIT SAME-OBJECT PAYMENT
------------------------------------------------------------------------

record StaticAnchorCandidateDiscoveryReceipt : Set where
  constructor static-anchor-candidate-discovery-receipt
  field
    runtimeReference : String
    staticConfidenceGateImplemented : Bool
    descriptorDistanceGateImplemented : Bool
    descriptorMarginGateImplemented : Bool
    mutualNearestCheckImplemented : Bool
    ambiguousCandidateCanAbstain : Bool
    sourceProvenanceRetained : Bool
    targetProvenanceRetained : Bool
    outputPaysSameObjectIdentity : Bool

open StaticAnchorCandidateDiscoveryReceipt public

currentStaticAnchorCandidateDiscoveryReceipt : StaticAnchorCandidateDiscoveryReceipt
currentStaticAnchorCandidateDiscoveryReceipt =
  static-anchor-candidate-discovery-receipt
    "chboishabba/animalexic/scripts/static_anchor_candidates.py"
    true true true true true true true false

record TemporalCandidateTrackReceipt : Set where
  constructor temporal-candidate-track-receipt
  field
    sameCameraTrackRequired : Bool
    maximumTimeGapGateImplemented : Bool
    descriptorContinuityGateImplemented : Bool
    ambiguityTerminatesTrackExtension : Bool
    provenanceChainRetained : Bool
    temporalTrackPaysSameObjectIdentity : Bool

open TemporalCandidateTrackReceipt public

currentTemporalCandidateTrackReceipt : TemporalCandidateTrackReceipt
currentTemporalCandidateTrackReceipt =
  temporal-candidate-track-receipt true true true true true false

------------------------------------------------------------------------
-- The only implemented bridge into the existing robust world-weld anchor
-- carrier consumes an explicit external same-object receipt.  The receipt must
-- match source feature ID, target feature ID, source provenance and target
-- provenance exactly, and both feature observations must carry finite local 3D
-- coordinates.  Ambiguous/abstained candidates cannot cross this seam.
------------------------------------------------------------------------

record SameObjectPaymentSeamReceipt : Set where
  constructor same-object-payment-seam-receipt
  field
    exactSourceFeatureIdentityRequired : Bool
    exactTargetFeatureIdentityRequired : Bool
    exactSourceProvenanceRequired : Bool
    exactTargetProvenanceRequired : Bool
    nonemptyAnchorIDRequired : Bool
    nonemptyPaymentReceiptReferenceRequired : Bool
    local3DPointRequiredOnBothSides : Bool
    ambiguousCandidateRejected : Bool
    abstainedCandidateRejected : Bool
    existingStaticAnchorObservationCarrierReused : Bool
    outputRemainsCandidate : Bool

open SameObjectPaymentSeamReceipt public

currentSameObjectPaymentSeamReceipt : SameObjectPaymentSeamReceipt
currentSameObjectPaymentSeamReceipt =
  same-object-payment-seam-receipt
    true true true true true true true true true true true

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data DescriptorCandidateImpliesSameObjectPermission : Set where

data TemporalTrackImpliesSameObjectPermission : Set where

data MutualNearestImpliesSameObjectPermission : Set where

data LowDescriptorDistanceImpliesSameObjectPermission : Set where

data SameObjectReceiptImpliesPromotedWorldWeldPermission : Set where

descriptorCandidateDoesNotPaySameObject :
  DescriptorCandidateImpliesSameObjectPermission → ⊥
descriptorCandidateDoesNotPaySameObject ()

temporalTrackDoesNotPaySameObject :
  TemporalTrackImpliesSameObjectPermission → ⊥
temporalTrackDoesNotPaySameObject ()

mutualNearestDoesNotPaySameObject :
  MutualNearestImpliesSameObjectPermission → ⊥
mutualNearestDoesNotPaySameObject ()

lowDescriptorDistanceDoesNotPaySameObject :
  LowDescriptorDistanceImpliesSameObjectPermission → ⊥
lowDescriptorDistanceDoesNotPaySameObject ()

sameObjectReceiptDoesNotPromoteWorldWeld :
  SameObjectReceiptImpliesPromotedWorldWeldPermission → ⊥
sameObjectReceiptDoesNotPromoteWorldWeld ()

------------------------------------------------------------------------
-- Implementation frontier.
------------------------------------------------------------------------

record StaticAnchorCandidateRoadmapStatus : Set where
  constructor static-anchor-candidate-roadmap-status
  field
    crossCameraDescriptorCandidateProducerImplemented : Bool
    ambiguousAbstentionImplemented : Bool
    temporalCandidateTracksImplemented : Bool
    exactSameObjectPaymentAdapterImplemented : Bool
    paidCandidateCanEnterExistingAnchorAssociation : Bool
    exactContentMirrorTestsPassed : String
    automaticSameObjectPaymentImplemented : Bool
    realImageDescriptorProducerIntegrated : Bool
    issue20AnchorDiscoveryValidated : Bool
    realMultiphoneAnchorDiscoveryValidated : Bool

open StaticAnchorCandidateRoadmapStatus public

currentStaticAnchorCandidateRoadmapStatus : StaticAnchorCandidateRoadmapStatus
currentStaticAnchorCandidateRoadmapStatus =
  static-anchor-candidate-roadmap-status
    true true true true true
    "5/5 static-anchor candidate/payment tests"
    false false false false

record StaticAnchorCandidateNextResidual : Set where
  constructor static-anchor-candidate-next-residual
  field
    connectImageFeatureProducer : Bool
    retainDescriptorProvenanceAcrossKeyframes : Bool
    defineOperatorOrGroundTruthSameObjectReceiptSource : Bool
    exerciseThreePlusPaidAnchorsThroughRobustWeld : Bool
    measureIdentityAmbiguityVersusGuardConsumerFrontier : Bool

open StaticAnchorCandidateNextResidual public

currentStaticAnchorCandidateNextResidual : StaticAnchorCandidateNextResidual
currentStaticAnchorCandidateNextResidual =
  static-anchor-candidate-next-residual true true true true true
