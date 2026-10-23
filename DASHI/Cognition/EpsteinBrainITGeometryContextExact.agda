module DASHI.Cognition.EpsteinBrainITGeometryContextExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Biology.NeuralRepresentationLaplacianExact as Neural

------------------------------------------------------------------------
-- BRAIN-IT / REPRESENTATION-GEOMETRY CONTEXT
--
-- Brain-IT (ICLR 2026; Beliy et al.) reconstructs viewed images from fMRI using
-- shared clusters of functionally similar voxels and a Brain Interaction
-- Transformer.  This owner does not import PR #1121 so the current branch stays
-- self-contained; it records only the source-level methodological bridge.
------------------------------------------------------------------------

data BrainReconstructionClaim : Set where
  viewedImageReconstruction : BrainReconstructionClaim
  sharedFunctionalClusters : BrainReconstructionClaim
  functionalClusterGeometry : BrainReconstructionClaim
  semanticStructuralDualBranch : BrainReconstructionClaim
  oneHourTransfer : BrainReconstructionClaim

record BrainITReceipt : Set where
  constructor brain-it-receipt
  field
    sourceName : String
    viewedStimulusOnly : Bool
    usesFMRI : Bool
    sharedClustersAcrossSubjects : Bool
    clusterCount128Reported : Bool
    oneHourNewSubjectTransfer : Bool
    comparableFortyHourBaseline : Bool
    arbitraryThoughtReadout : Bool
    dreamReadoutEstablished : Bool
open BrainITReceipt public

brainIT2026Receipt : BrainITReceipt
brainIT2026Receipt = brain-it-receipt
  "Brain-IT: Image Reconstruction from fMRI via Brain-Interaction Transformer"
  true true true true true true false false

-- Existing repo geometry boundary: coarse observations are many-to-one and do
-- not recover the microscopic neural state.
coarseObserverBoundary : Neural.NeuralLaplacianBoundary
coarseObserverBoundary = Neural.canonicalNeuralLaplacianBoundary

------------------------------------------------------------------------
-- GEOMETRIC-REASONING CONNECTION
--
-- The useful commonality is representational geometry: success can come from a
-- structured latent carrier / symbolic or cluster geometry without that carrier
-- being identical to the underlying physical mechanism.  This is analogous to
-- current AI geometry work that separates diagram perception, symbolic carrier,
-- and logical deduction.
------------------------------------------------------------------------

record RepresentationGeometryBridge : Set where
  constructor representation-geometry-bridge
  field
    structuredLatentCarrierUseful : Bool
    sharedRepresentationSupportsTransfer : Bool
    geometryCanAidGeneralisation : Bool
    representationEqualsPhysicalMechanism : Bool
    decodedOutputEqualsOriginalMentalState : Bool
open RepresentationGeometryBridge public

canonicalRepresentationGeometryBridge : RepresentationGeometryBridge
canonicalRepresentationGeometryBridge =
  representation-geometry-bridge true true true false false

------------------------------------------------------------------------
-- EPSTEIN/YU BOUNDARY
------------------------------------------------------------------------

record EpsteinYuBrainITContext : Set where
  constructor epstein-yu-brain-it-context
  field
    yuIndependentEEGFMRIBackground : Bool
    epsteinYuBrainITUseEstablished : Bool
    epsteinYuViewedImageDecoderEstablished : Bool
    epsteinYuThoughtDecoderEstablished : Bool
open EpsteinYuBrainITContext public

currentEpsteinYuBrainITContext : EpsteinYuBrainITContext
currentEpsteinYuBrainITContext =
  epstein-yu-brain-it-context true false false false

------------------------------------------------------------------------
-- PROMOTION FIREWALLS
------------------------------------------------------------------------

data ViewedImageReconstructionImpliesThoughtReading : Set where
data RepresentationGeometryImpliesMechanism : Set where
data SharedClustersImpliesUniversalBrainCode : Set where
data ModernMethodImpliesHistoricalUse : Set where

reconstructionDoesNotEstablishThoughtReading :
  ViewedImageReconstructionImpliesThoughtReading → ⊥
reconstructionDoesNotEstablishThoughtReading ()

representationGeometryDoesNotEstablishMechanism :
  RepresentationGeometryImpliesMechanism → ⊥
representationGeometryDoesNotEstablishMechanism ()

sharedClustersDoNotEstablishUniversalBrainCode :
  SharedClustersImpliesUniversalBrainCode → ⊥
sharedClustersDoNotEstablishUniversalBrainCode ()

modernMethodDoesNotEstablishHistoricalEpsteinYuUse :
  ModernMethodImpliesHistoricalUse → ⊥
modernMethodDoesNotEstablishHistoricalEpsteinYuUse ()
