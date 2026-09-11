module DASHI.Biology.BioacousticAreseSharedManifoldProducerExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Biology.BioacousticAnimalexicTrajectoryBridgeExact as Bridge

------------------------------------------------------------------------
-- Source-exact receipt for Lucio Arese's current v4 shared-manifold pipeline.
--
-- This owner records the published producer shape needed by the Animalexic
-- importer.  It does not re-run the analysis, prove UMAP fidelity, or promote
-- a deposited CSV into canonical DASHI/Animalexic evidence.
------------------------------------------------------------------------

record PublishedBioacousticProducerReceipt : Set where
  constructor publishedBioacousticProducerReceipt
  field
    author : String
    title : String
    paperDOI : String
    dataDOI : String
    publicationState : String
    dataAvailability : String
    sourceRole : String

open PublishedBioacousticProducerReceipt public

areseProducerReceipt : PublishedBioacousticProducerReceipt
areseProducerReceipt =
  publishedBioacousticProducerReceipt
    "Lucio Arese"
    "Shared acoustic manifolds for exploratory comparison of passerine vocalizations"
    "10.32942/X2W65N"
    "10.5281/zenodo.18332166"
    "EcoEvoRxiv preprint, current web-visible version 4"
    "processed shared-embedding coordinates and frame-aligned descriptors deposited as CSV; supplementary videos also deposited"
    "external real-data trajectory producer; attribution/custody receipt, not local theorem authority"

------------------------------------------------------------------------
-- Feature / reduction method receipt.
------------------------------------------------------------------------

data FeatureFamily : Set where
  mfcc120 : FeatureFamily
  chroma80 : FeatureFamily

data DistanceMetric : Set where
  euclidean : DistanceMetric
  cosine : DistanceMetric

record SharedManifoldMethod : Set where
  constructor sharedManifoldMethod
  field
    featureFamily : FeatureFamily
    sourceDimensions : Nat
    featureConstruction : String
    pcaDimensions : Nat
    umapDimensions : Nat
    umapNeighbors : Nat
    umapMinDist : String
    randomSeed : Nat
    metric : DistanceMetric
    normalization : String
    concatenationScope : String
    trajectorySemantics : String

open SharedManifoldMethod public

areseMFCCMethod : SharedManifoldMethod
areseMFCCMethod =
  sharedManifoldMethod
    mfcc120
    120
    "40 MFCC coefficients plus delta plus delta-delta"
    20
    3
    30
    "0.1"
    42
    euclidean
    "shared/global unit-cube coordinate normalization after reduction"
    "frames from four individuals concatenated per species before shared UMAP fit"
    "time-ordered per-recording trajectory through the shared species manifold"

areseChromaMethod : SharedManifoldMethod
areseChromaMethod =
  sharedManifoldMethod
    chroma80
    80
    "80-bin EDO chroma, L1-normalized"
    20
    3
    30
    "0.1"
    42
    cosine
    "shared/global unit-cube coordinate normalization after reduction"
    "frames from four individuals concatenated per species before shared UMAP fit"
    "time-ordered per-recording trajectory through the shared species manifold"

canonicalAreseMethods : List SharedManifoldMethod
canonicalAreseMethods = areseMFCCMethod ∷ areseChromaMethod ∷ []

------------------------------------------------------------------------
-- Visualization-only descriptors remain outside the embedding input fibre.
------------------------------------------------------------------------

data OverlayDescriptor : Set where
  rms : OverlayDescriptor
  spectralCentroid : OverlayDescriptor
  chromaEnergyConcentration : OverlayDescriptor

overlayReading : OverlayDescriptor → String
overlayReading rms = "RMS controls/annotates visual point size; it is not an embedding input"
overlayReading spectralCentroid = "spectral centroid is a scalar-field color overlay; it does not alter manifold geometry"
overlayReading chromaEnergyConcentration = "CEC is a chroma-derived scalar-field color overlay; it does not alter manifold geometry"

canonicalOverlays : List OverlayDescriptor
canonicalOverlays = rms ∷ spectralCentroid ∷ chromaEnergyConcentration ∷ []

------------------------------------------------------------------------
-- Species / same-space scope.
------------------------------------------------------------------------

data SpeciesGroup : Set where
  eurasianWren : SpeciesGroup
  treePipit : SpeciesGroup
  commonChaffinch : SpeciesGroup

speciesReading : SpeciesGroup → String
speciesReading eurasianWren = "Troglodytes troglodytes / Eurasian Wren"
speciesReading treePipit = "Anthus trivialis / Tree Pipit"
speciesReading commonChaffinch = "Fringilla coelebs / Common Chaffinch"

canonicalSpecies : List SpeciesGroup
canonicalSpecies = eurasianWren ∷ treePipit ∷ commonChaffinch ∷ []

------------------------------------------------------------------------
-- Data-to-Animalexic handoff.
------------------------------------------------------------------------

record AreseCandidateImportBoundary : Set where
  constructor areseCandidateImportBoundary
  field
    publishedCSVIsRealExternalData : Bool
    publishedCSVIsRealExternalDataIsTrue : publishedCSVIsRealExternalData ≡ true

    publishedCSVIsAnimalexicPromotionReceipt : Bool
    publishedCSVIsAnimalexicPromotionReceiptIsFalse :
      publishedCSVIsAnimalexicPromotionReceipt ≡ false

    depositedCoordinateIsPhysicalCoordinate : Bool
    depositedCoordinateIsPhysicalCoordinateIsFalse :
      depositedCoordinateIsPhysicalCoordinate ≡ false

    embeddingNeighbourhoodIsSpeciesIdentity : Bool
    embeddingNeighbourhoodIsSpeciesIdentityIsFalse :
      embeddingNeighbourhoodIsSpeciesIdentity ≡ false

    overlayDescriptorChangesEmbeddingGeometry : Bool
    overlayDescriptorChangesEmbeddingGeometryIsFalse :
      overlayDescriptorChangesEmbeddingGeometry ≡ false

    candidateDiagnosticRenderingAllowed : Bool
    candidateDiagnosticRenderingAllowedIsTrue :
      candidateDiagnosticRenderingAllowed ≡ true

    canonicalMutationStillRequiresAnimalexicPromotion : Bool
    canonicalMutationStillRequiresAnimalexicPromotionIsTrue :
      canonicalMutationStillRequiresAnimalexicPromotion ≡ true

open AreseCandidateImportBoundary public

canonicalAreseCandidateImportBoundary : AreseCandidateImportBoundary
canonicalAreseCandidateImportBoundary =
  areseCandidateImportBoundary
    true refl
    false refl
    false refl
    false refl
    false refl
    true refl
    true refl

------------------------------------------------------------------------
-- Reuse the cross-repository ABI rather than introducing another row type.
------------------------------------------------------------------------

trajectoryABI : Bridge.AnimalexicTrajectoryABI
trajectoryABI = Bridge.canonicalAnimalexicTrajectoryABI

externalProducer : Bridge.ExternalTrajectoryProducer
externalProducer = Bridge.areseSharedAcousticManifolds

producerStatement : String
producerStatement =
  "Arese v4 supplies a real published frame-level shared-manifold producer: MFCC120 or chroma80 -> PCA20 -> UMAP3, with time-ordered per-recording trajectories. Animalexic imports deposited coordinates as provenance-bearing candidates first; source publication, DOI identity, visual recurrence, and embedding proximity do not themselves pay promotion, taxonomy, physical-coordinate, or causal claims."
