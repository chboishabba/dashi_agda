module DASHI.Biology.BrainITConnectomeFMRIWeldExact where

open import DASHI.Core.Prelude

import DASHI.Biology.BrainITFunctionalClusterTransferExact as BrainIT
import DASHI.Biology.FunctionalConnectomeBodyMemoryBridge as Connectome
import DASHI.Physics.Closure.BidirectionalBrainObservationQuotient as Bidirectional
import DASHI.Physics.Closure.BrainConnectomeFMRIObservationQuotient as BrainFMRI

------------------------------------------------------------------------
-- Brain-IT is placed inside the pre-existing DASHI brain/fMRI quotient stack.
--
-- The important type separation is:
--   structural/functional connectome graph carrier
--   != learned Brain-IT functional-cluster coordinate system
--   != BOLD/fMRI observation quotient
--   != latent microscopic brain/body state.
--
-- This module therefore strengthens the original Brain-IT tranche by reusing
-- the existing connectome and bidirectional observation machinery rather than
-- introducing a parallel neural ontology.

brainITFMRIParentBoundary : BrainFMRI.BrainConnectomeFMRIObservationBoundary
brainITFMRIParentBoundary =
  BrainFMRI.canonicalBrainConnectomeFMRIObservationBoundary

brainITBidirectionalParentBoundary :
  Bidirectional.BidirectionalBrainObservationBoundary
brainITBidirectionalParentBoundary =
  Bidirectional.canonicalBidirectionalBrainObservationBoundary

brainITConnectomeParentBridge :
  Connectome.FunctionalConnectomeBodyMemoryBridge
brainITConnectomeParentBridge =
  Connectome.canonicalFunctionalConnectomeBodyMemoryBridge

brainITFunctionalClusterCount : Nat
brainITFunctionalClusterCount =
  BrainIT.functionalClusterCount BrainIT.canonicalBrainITArchitecture

brainITFunctionalClusterCountIs128 :
  brainITFunctionalClusterCount ≡ 128
brainITFunctionalClusterCountIs128 = refl

------------------------------------------------------------------------
-- Functional clusters are learned shared coordinates over measured fMRI.
-- They are not promoted to literal anatomical fibres, synapses, structural
-- connectome edges, or uniquely recovered latent neural states.

record BrainITConnectomePlacementBoundary : Set where
  constructor brainITConnectomePlacementBoundary
  field
    functionalClustersAreLearnedSharedCoordinates : Bool
    functionalClustersAreLearnedSharedCoordinatesIsTrue :
      functionalClustersAreLearnedSharedCoordinates ≡ true

    functionalClustersAreStructuralConnectomeEdges : Bool
    functionalClustersAreStructuralConnectomeEdgesIsFalse :
      functionalClustersAreStructuralConnectomeEdges ≡ false

    functionalClustersAreAnatomicalRegions : Bool
    functionalClustersAreAnatomicalRegionsIsFalse :
      functionalClustersAreAnatomicalRegions ≡ false

    sharedClustersRecoverLatentBrainState : Bool
    sharedClustersRecoverLatentBrainStateIsFalse :
      sharedClustersRecoverLatentBrainState ≡ false

    brainITReadoutRemainsLossyObservation : Bool
    brainITReadoutRemainsLossyObservationIsTrue :
      brainITReadoutRemainsLossyObservation ≡ true

    crossSubjectTransferEliminatesIndividualVariation : Bool
    crossSubjectTransferEliminatesIndividualVariationIsFalse :
      crossSubjectTransferEliminatesIndividualVariation ≡ false

    connectomeGraphProxyNotIdentity :
      Connectome.proxyNotIdentity
        (Connectome.connectomeCarrier brainITConnectomeParentBridge)
      ≡ true

    parentFMRIIsObservationChannel :
      BrainFMRI.highResolutionFMRIIsObservationChannel
        brainITFMRIParentBoundary
      ≡ true

    parentLatentStateRecoveryBlocked :
      Bidirectional.latentStateRecovery
        brainITBidirectionalParentBoundary
      ≡ false

canonicalBrainITConnectomePlacementBoundary :
  BrainITConnectomePlacementBoundary
canonicalBrainITConnectomePlacementBoundary =
  brainITConnectomePlacementBoundary
    true refl
    false refl
    false refl
    false refl
    true refl
    false refl
    refl
    refl
    refl

------------------------------------------------------------------------
-- The existing graph carrier already distinguishes structural from functional
-- edges. Brain-IT's 128 learned clusters therefore live one level further out:
-- as coordinates used by a decoder on the fMRI measurement quotient.

record BrainITObservationFactorisation : Set where
  constructor brainITObservationFactorisation
  field
    latentBrainBodyProcess : String
    connectomeConstrainedProcessing : String
    fmriMeasurementQuotient : String
    learnedFunctionalClusterCoordinates : String
    imageReconstructionConsumer : String
    factorisationReading : String

canonicalBrainITObservationFactorisation : BrainITObservationFactorisation
canonicalBrainITObservationFactorisation =
  brainITObservationFactorisation
    "latent brain/body process: not uniquely recovered"
    "connectome-constrained neural processing: structural/functional graph carrier"
    "BOLD/fMRI measurement: many-to-one observation quotient"
    "Brain-IT 128 functional clusters: learned shared decoder coordinates"
    "viewed-image reconstruction: consumer of the measured quotient"
    "latent process -> connectome-constrained processing -> fMRI quotient -> learned functional-cluster coordinates -> viewed-image reconstruction; no arrow is promoted to an inverse of the latent process"

------------------------------------------------------------------------
-- Cross-pollination receipts. These state compatibility with the existing
-- brain programme while retaining the old fail-closed empirical boundaries.

brainITUsesExistingFMRIObservationPosture :
  BrainFMRI.highResolutionFMRIIsObservationChannel brainITFMRIParentBoundary
  ≡ true
brainITUsesExistingFMRIObservationPosture = refl

brainITRetainsNoLatentRecoveryBoundary :
  Bidirectional.latentStateRecovery brainITBidirectionalParentBoundary
  ≡ false
brainITRetainsNoLatentRecoveryBoundary = refl

brainITRetainsConnectomeProxyBoundary :
  Connectome.proxyNotIdentity
    (Connectome.connectomeCarrier brainITConnectomeParentBridge)
  ≡ true
brainITRetainsConnectomeProxyBoundary = refl

brainITSharedClustersRemainSubjectCalibrated :
  BrainIT.sharedClustersEliminateSubjectSpecificCalibration
    BrainIT.canonicalTransferInterpretationBoundary
  ≡ false
brainITSharedClustersRemainSubjectCalibrated = refl

------------------------------------------------------------------------
-- Max-cut status: Brain-IT pays a concrete learned decoder / transfer result
-- inside the observation quotient, but it does not pay the pre-existing
-- missing connectome dataset, latent-state, body-resource, or universal inverse
-- receipts. Those remain separate empirical obligations.

record BrainITConnectomeMaxCut : Set where
  constructor brainITConnectomeMaxCut
  field
    learnedClusterArchitecturePaid : Bool
    learnedClusterArchitecturePaidIsTrue :
      learnedClusterArchitecturePaid ≡ true

    oneHourCrossSubjectTransferPaid : Bool
    oneHourCrossSubjectTransferPaidIsTrue :
      oneHourCrossSubjectTransferPaid ≡ true

    structuralConnectomeIdentificationPaid : Bool
    structuralConnectomeIdentificationPaidIsFalse :
      structuralConnectomeIdentificationPaid ≡ false

    latentStateInversePaid : Bool
    latentStateInversePaidIsFalse :
      latentStateInversePaid ≡ false

    wholeBrainCognitionClosurePaid : Bool
    wholeBrainCognitionClosurePaidIsFalse :
      wholeBrainCognitionClosurePaid ≡ false

canonicalBrainITConnectomeMaxCut : BrainITConnectomeMaxCut
canonicalBrainITConnectomeMaxCut =
  brainITConnectomeMaxCut true refl true refl false refl false refl false refl
