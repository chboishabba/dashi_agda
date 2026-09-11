module DASHI.Reasoning.FibreRoutingGrokkingMoEBrainCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Biology.SparseExpertRoutingCoalition as MoE
import DASHI.Biology.SpectralGrokkingLatticeExact as Spectral
import DASHI.Reasoning.DASHIgGrokkingEmpiricalBridgeExact as DASHIg
import DASHI.Reasoning.StructuralMetaphorTaskCompressionExact as Compression
import DASHI.Reasoning.RelationRepresentationRealizationExact as Realization
import DASHI.Physics.Closure.LilaE8RootEnumerationNoDuplicatesSurface as LilaE8

------------------------------------------------------------------------
-- FIBRE ROUTING / GROKKING / MoE / BRAIN CROSS-POLLINATION
--
-- Shared structural grammar only:
--
--   candidate fibres / experts
--     -> context-relative routing or membership
--     -> fibre-local contribution
--     -> composition
--     -> consumer-relative evaluation.
--
-- The owner deliberately does NOT identify MoE with brains, grokking with MoE,
-- LILA/E8 with a routing mechanism, or predictive adequacy with biological
-- mechanism.  It reuses the existing realization owner for that final firewall.
------------------------------------------------------------------------

record FibreRoutingCarrier
    (Input Fibre Weight : Set) : Set₁ where
  constructor fibreRoutingCarrier
  field
    routeWeight : Input → Fibre → Weight
    overlappingMembershipPermitted : Bool
    routingReading : String

open FibreRoutingCarrier public

record FibreCompositionCarrier
    (Input Fibre Weight Contribution Representation : Set) : Set₁ where
  constructor fibreCompositionCarrier
  field
    routing : FibreRoutingCarrier Input Fibre Weight
    localContribution : Input → Fibre → Contribution
    compose :
      (Fibre → Weight) →
      (Fibre → Contribution) →
      Representation
    encode : Input → Representation
    compositionCommutes :
      (input : Input) →
      encode input ≡
      compose
        (routeWeight routing input)
        (localContribution input)
    compositionReading : String

open FibreCompositionCarrier public

------------------------------------------------------------------------
-- Fly/VFB overlapping painted-domain specimen.
--
-- This is the formal shape of the current dashiBRAIN soft-carrier producer:
-- one selected ROI may carry non-zero membership in both a parent and a nested
-- child painted domain.  Nothing here requires memberships to sum to one.
------------------------------------------------------------------------

data PaintedDomain : Set where
  parentDomain : PaintedDomain
  childDomain : PaintedDomain

data SoftMembership : Set where
  zeroMembership : SoftMembership
  halfMembership : SoftMembership
  fullMembership : SoftMembership

data SelectedROISpecimen : Set where
  overlappingROI : SelectedROISpecimen
  parentOnlyROI : SelectedROISpecimen

paintedMembership :
  SelectedROISpecimen →
  PaintedDomain →
  SoftMembership
paintedMembership overlappingROI parentDomain = fullMembership
paintedMembership overlappingROI childDomain = halfMembership
paintedMembership parentOnlyROI parentDomain = fullMembership
paintedMembership parentOnlyROI childDomain = zeroMembership

data ActiveMembership : SoftMembership → Set where
  halfMembershipActive : ActiveMembership halfMembership
  fullMembershipActive : ActiveMembership fullMembership

overlappingROIActivatesParentAndChild :
  ActiveMembership (paintedMembership overlappingROI parentDomain)
  × ActiveMembership (paintedMembership overlappingROI childDomain)
overlappingROIActivatesParentAndChild =
  fullMembershipActive , halfMembershipActive

flySoftRoutingCarrier :
  FibreRoutingCarrier SelectedROISpecimen PaintedDomain SoftMembership
flySoftRoutingCarrier =
  fibreRoutingCarrier
    paintedMembership
    true
    "VFB painted domains are retained as overlapping functional fibres; a selected ROI may contribute to more than one painted domain and memberships are not forced to sum to one."

------------------------------------------------------------------------
-- Why unique-maximum collapse is a genuine information-loss operation.
--
-- Two fine ROI states can share one hard winner while differing in the richer
-- overlap profile.  Therefore the hard winner cannot realize the overlap
-- profile for every fine state.
------------------------------------------------------------------------

data HardPaintedIdentity : Set where
  parentWinner : HardPaintedIdentity

data PaintedOverlapProfile : Set where
  parentAndChildProfile : PaintedOverlapProfile
  parentOnlyProfile : PaintedOverlapProfile

hardPaintedIdentity : SelectedROISpecimen → HardPaintedIdentity
hardPaintedIdentity overlappingROI = parentWinner
hardPaintedIdentity parentOnlyROI = parentWinner

paintedOverlapProfile : SelectedROISpecimen → PaintedOverlapProfile
paintedOverlapProfile overlappingROI = parentAndChildProfile
paintedOverlapProfile parentOnlyROI = parentOnlyProfile

hardWinnerLosesOverlapProfile :
  Compression.CompressionFailureWitness
    hardPaintedIdentity paintedOverlapProfile
hardWinnerLosesOverlapProfile =
  Compression.compressionFailureWitness
    overlappingROI
    parentOnlyROI
    refl
    (λ ())

hardWinnerCannotRealizeOverlapProfile :
  Realization.RepresentationRealizationWitness
    hardPaintedIdentity paintedOverlapProfile → ⊥
hardWinnerCannotRealizeOverlapProfile =
  Realization.representationCollisionBlocksRealization
    hardWinnerLosesOverlapProfile

softOverlapProfileRealizesItself :
  Realization.RepresentationRealizationWitness
    paintedOverlapProfile paintedOverlapProfile
softOverlapProfileRealizesItself =
  Realization.representationRealizationWitness
    (λ profile → profile)
    (λ _ → refl)
    "The overlap profile is retained as the representation itself; this witness is only a finite semantic specimen, not a claim that atlas overlap is a complete biological mechanism."

------------------------------------------------------------------------
-- Existing MoE donor: sparse production does not require every expert active.
------------------------------------------------------------------------

sensoryRouteRemainsSparse :
  MoE.sensoryRouteCount ≤ MoE.allExpertCount
sensoryRouteRemainsSparse = MoE.sensoryRouteIsSparse

reflectiveRouteRemainsSparse :
  MoE.reflectiveRouteCount ≤ MoE.allExpertCount
reflectiveRouteRemainsSparse = MoE.reflectiveRouteIsSparse

brainMoERemainsAnalogyOnly :
  MoE.literalBrainMoEArchitecturePromoted
    MoE.canonicalSparseExpertCoalitionBoundary ≡ false
brainMoERemainsAnalogyOnly =
  MoE.literalBrainMoEArchitecturePromotedIsFalse
    MoE.canonicalSparseExpertCoalitionBoundary

------------------------------------------------------------------------
-- Existing grokking donor: cleanup removes irregular components while retaining
-- symmetry-adapted modes.  We consume the fact without promoting it into a
-- universal MoE routing theorem.
------------------------------------------------------------------------

cleanupRemovesIrregularComponents :
  Spectral.irregularComponentCount Spectral.cleanupPhase ≡ 0
cleanupRemovesIrregularComponents =
  Spectral.cleanupRemovesIrregularComponents

cleanupRetainsSymmetryModes :
  Spectral.symmetryAdaptedComponentCount Spectral.cleanupPhase ≡ 3
cleanupRetainsSymmetryModes =
  Spectral.cleanupRetainsThreeSymmetryModes

------------------------------------------------------------------------
-- DASHIg empirical producer is pinned separately from the formal grammar.
------------------------------------------------------------------------

dashigPinnedProducerRepository : String
dashigPinnedProducerRepository =
  DASHIg.repository DASHIg.canonicalDASHIgPhase2Source

dashigPinnedProducerCommit : String
dashigPinnedProducerCommit =
  DASHIg.commit DASHIg.canonicalDASHIgPhase2Source

------------------------------------------------------------------------
-- LILA/E8 contributes an admissible geometric carrier specimen.  It is not
-- treated as the router, the learned expert family, or an explanation of the
-- Fly result.  Its current closure status remains exactly the upstream status.
------------------------------------------------------------------------

lilaE8FiniteCarrierStatus : LilaE8.LilaE8NoDuplicatesSurfaceStatus
lilaE8FiniteCarrierStatus =
  LilaE8.executableIndexedNoDuplicatesAvailableCompletenessBlocked

------------------------------------------------------------------------
-- Cross-repo runtime provenance for the current Fly soft-carrier refinement.
------------------------------------------------------------------------

record FlyRuntimeProducer : Set where
  constructor flyRuntimeProducer
  field
    repository : String
    commit : String
    functionalOwner : String
    compiler : String
    boundedReading : String

open FlyRuntimeProducer public

canonicalFlySoftCarrierProducer : FlyRuntimeProducer
canonicalFlySoftCarrierProducer =
  flyRuntimeProducer
    "github.com/chboishabba/dashiBRAIN"
    "e44b3fe57aa6457d6ef543219f01e70395d6dce8"
    "dashi/analysis/jrc2018_painted_fibre.py"
    "scripts/compile_gauthey_jrc2018_regions.py --carrier soft"
    "Produces overlapping painted-domain functional membership from the same transformed exact selected-supervoxel carrier; does not establish neuron identity, biological mechanism, or population generalization."

------------------------------------------------------------------------
-- Shared interpretation boundary.
------------------------------------------------------------------------

record FibreRoutingCrossPollinationBoundary : Set where
  constructor fibreRoutingCrossPollinationBoundary
  field
    mixtureOfExpertsIsLiteralBrainArchitecture : Bool
    mixtureOfExpertsIsLiteralBrainArchitectureIsFalse :
      mixtureOfExpertsIsLiteralBrainArchitecture ≡ false

    grokkingIsDefinitionallyMixtureOfExperts : Bool
    grokkingIsDefinitionallyMixtureOfExpertsIsFalse :
      grokkingIsDefinitionallyMixtureOfExperts ≡ false

    lilaE8ExplainsFlyStructureFunctionResult : Bool
    lilaE8ExplainsFlyStructureFunctionResultIsFalse :
      lilaE8ExplainsFlyStructureFunctionResult ≡ false

    overlappingAtlasImpliesUniqueRegionIdentity : Bool
    overlappingAtlasImpliesUniqueRegionIdentityIsFalse :
      overlappingAtlasImpliesUniqueRegionIdentity ≡ false

    hardWinnerCanEraseConsumerRelevantOverlap : Bool
    hardWinnerCanEraseConsumerRelevantOverlapIsTrue :
      hardWinnerCanEraseConsumerRelevantOverlap ≡ true

    routingMayBeConsumerAndContextRelative : Bool
    routingMayBeConsumerAndContextRelativeIsTrue :
      routingMayBeConsumerAndContextRelative ≡ true

    learningMayChangeWhichFibresCarryTheConsumer : Bool
    learningMayChangeWhichFibresCarryTheConsumerIsTrue :
      learningMayChangeWhichFibresCarryTheConsumer ≡ true

    heldOutAdequacyImpliesPhysicalMechanism : Bool
    heldOutAdequacyImpliesPhysicalMechanismIsFalse :
      heldOutAdequacyImpliesPhysicalMechanism ≡ false

    explicitRealizationWitnessStillRequired : Bool
    explicitRealizationWitnessStillRequiredIsTrue :
      explicitRealizationWitnessStillRequired ≡ true

canonicalFibreRoutingCrossPollinationBoundary :
  FibreRoutingCrossPollinationBoundary
canonicalFibreRoutingCrossPollinationBoundary =
  fibreRoutingCrossPollinationBoundary
    false refl
    false refl
    false refl
    false refl
    true refl
    true refl
    true refl
    false refl
    true refl
