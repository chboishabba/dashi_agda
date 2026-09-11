module DASHI.Biology.DrosophilaGautheyFunctionalTrajectoryProducerExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Biology.BioacousticAnimalexicTrajectoryBridgeExact as Bridge
import DASHI.Biology.DrosophilaGautheyCompactArchiveReceiptExact as Gauthey

------------------------------------------------------------------------
-- Thin state-space producer over the already-pinned Gauthey compact archive.
--
-- The source matrix is 940 selected ROI rows x 668 time samples.  The visual
-- diagnostic treats each time column as a 940-dimensional functional state and
-- projects those timepoints to 3D with an explicitly downstream PCA producer.
-- Nothing here upgrades selected ROI identity to a MaleCNS neuron identity.
------------------------------------------------------------------------

record FunctionalTrajectoryProjection : Set where
  constructor functionalTrajectoryProjection
  field
    inputRows : Nat
    timeSamples : Nat
    inputAxisSemantics : String
    projectionName : String
    outputDimensions : Nat
    centering : String
    trajectorySemantics : String

open FunctionalTrajectoryProjection public

canonicalGautheyPCA3Projection : FunctionalTrajectoryProjection
canonicalGautheyPCA3Projection =
  functionalTrajectoryProjection
    940
    668
    "selected-roi-by-time; selected ROI identity is not registered to MaleCNS"
    "mean-centered PCA over timepoint vectors"
    3
    "subtract per-selected-ROI temporal mean before SVD/PCA"
    "one candidate visual trajectory point per source time sample"

sourceArchiveReceipt : Gauthey.GautheyCompactArchiveReceipt
sourceArchiveReceipt = Gauthey.canonicalGautheyCompactArchiveReceipt

record GautheyFunctionalTrajectoryBoundary : Set where
  constructor gautheyFunctionalTrajectoryBoundary
  field
    publishedPreprocessedMatrixIsRealFunctionalData : Bool
    publishedPreprocessedMatrixIsRealFunctionalDataIsTrue :
      publishedPreprocessedMatrixIsRealFunctionalData ≡ true

    selectedROIRowIsMaleCNSNeuron : Bool
    selectedROIRowIsMaleCNSNeuronIsFalse :
      selectedROIRowIsMaleCNSNeuron ≡ false

    pcaCoordinateIsAnatomicalCoordinate : Bool
    pcaCoordinateIsAnatomicalCoordinateIsFalse :
      pcaCoordinateIsAnatomicalCoordinate ≡ false

    visualRecurrenceIdentifiesSameNeuronPopulation : Bool
    visualRecurrenceIdentifiesSameNeuronPopulationIsFalse :
      visualRecurrenceIdentifiesSameNeuronPopulation ≡ false

    functionalActivationProvesCausalNecessity : Bool
    functionalActivationProvesCausalNecessityIsFalse :
      functionalActivationProvesCausalNecessity ≡ false

    sourcePublicationIsAnimalexicPromotionReceipt : Bool
    sourcePublicationIsAnimalexicPromotionReceiptIsFalse :
      sourcePublicationIsAnimalexicPromotionReceipt ≡ false

    diagnosticCandidateRenderingAllowed : Bool
    diagnosticCandidateRenderingAllowedIsTrue :
      diagnosticCandidateRenderingAllowed ≡ true

    laterRegistrationRequiresSeparateReceipt : Bool
    laterRegistrationRequiresSeparateReceiptIsTrue :
      laterRegistrationRequiresSeparateReceipt ≡ true

open GautheyFunctionalTrajectoryBoundary public

canonicalGautheyFunctionalTrajectoryBoundary : GautheyFunctionalTrajectoryBoundary
canonicalGautheyFunctionalTrajectoryBoundary =
  gautheyFunctionalTrajectoryBoundary
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
    true refl

trajectoryABI : Bridge.AnimalexicTrajectoryABI
trajectoryABI = Bridge.canonicalAnimalexicTrajectoryABI

producerStatement : String
producerStatement =
  "The pinned Gauthey 940 x 668 selected-ROI-by-time matrix can feed a declared downstream PCA-3 candidate trajectory for visual inspection. The source matrix is real functional data, but selected ROI rows remain unregistered to MaleCNS neuron identities; PCA geometry, recurrence, source publication, and functional activation do not manufacture anatomical identity, promotion, or causality."
