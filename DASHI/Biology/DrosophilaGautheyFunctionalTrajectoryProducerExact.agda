module DASHI.Biology.DrosophilaGautheyFunctionalTrajectoryProducerExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
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

------------------------------------------------------------------------
-- Source-code archaeology: the public analysis repository pays a common
-- protocol-aligned time axis for the conventional-2P pooled matrix.
--
-- Fig3_aligment.py aligns each source trial by sound-server frame and I2C time,
-- and exports time_audio_aligned / time_activity_align. fig3_preprocessing.py
-- then uses four named 2P trials, truncates each to min_dim=668 at
-- Hz=2.20337115787, stacks ROI rows, constructs the 13 stimulus blocks on the
-- aligned time axis, and finally exports only dffs_all[audio_correlated, :].
--
-- Therefore protocol/time-sample alignment is paid for the pooled matrix, but
-- the selected-row -> source trial / plane / ROI identity is not paid because
-- the selection indices are not retained in that compact export.
------------------------------------------------------------------------

record GautheyTimebaseSourceReceipt : Set where
  constructor gautheyTimebaseSourceReceipt
  field
    codeRepository : String
    repositoryTreeIdentity : String
    fig3AlignmentBlob : String
    fig3PreprocessingBlob : String
    stimulusCarrier : String
    stimulusCarrierBlob : String
    conventional2PSampleRate : String
    sourceTrialReferences : List String
    stimulusBlockReference : String
    pooledTimeSamples : Nat
    pooledProtocolTimebasePaid : Bool
    pooledRowSourceIdentityPaid : Bool

open GautheyTimebaseSourceReceipt public

canonicalGautheyTimebaseSourceReceipt : GautheyTimebaseSourceReceipt
canonicalGautheyTimebaseSourceReceipt =
  gautheyTimebaseSourceReceipt
    "https://github.com/murthylab/lightbead-analysis"
    "main tree 55570f4ad028bfd19ab63d5b9b13430803cb277c"
    "f34fe193f0507b5ad7f3c05d6b8973c04a34cf02"
    "39a4ae6739b9e13040b971469616e908df41f502"
    "Data/Stimulus/highspeed_pulse_2_WG_paper_forplotting.mat"
    "57a3052ba0a9b3503a04a6c50de5255fadcd4d19"
    "2.20337115787 Hz"
    ("GCaMP6f_12132024_a2_r2.pkl" ∷
     "GCaMP6f_12132024_a2_r3.pkl" ∷
     "GCaMP6f_12132024_a2_r4.pkl" ∷
     "GCaMP6f_12202024_a1_r2.pkl" ∷ [])
    "13 source blocks: starts 5,25,45,65,84,103,123,143,163,183,202.99894,222.99788,242.99788 s; corresponding approximately 10 s ends"
    668
    true
    false

record GautheyFunctionalTrajectoryBoundary : Set where
  constructor gautheyFunctionalTrajectoryBoundary
  field
    publishedPreprocessedMatrixIsRealFunctionalData : Bool
    publishedPreprocessedMatrixIsRealFunctionalDataIsTrue :
      publishedPreprocessedMatrixIsRealFunctionalData ≡ true

    pooledProtocolTimebaseRecovered : Bool
    pooledProtocolTimebaseRecoveredIsTrue :
      pooledProtocolTimebaseRecovered ≡ true

    protocolTimeAlignmentRecoversPooledRowSourceIdentity : Bool
    protocolTimeAlignmentRecoversPooledRowSourceIdentityIsFalse :
      protocolTimeAlignmentRecoversPooledRowSourceIdentity ≡ false

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

    laterRowIdentityAndRegistrationRequireSeparateReceipt : Bool
    laterRowIdentityAndRegistrationRequireSeparateReceiptIsTrue :
      laterRowIdentityAndRegistrationRequireSeparateReceipt ≡ true

open GautheyFunctionalTrajectoryBoundary public

canonicalGautheyFunctionalTrajectoryBoundary : GautheyFunctionalTrajectoryBoundary
canonicalGautheyFunctionalTrajectoryBoundary =
  gautheyFunctionalTrajectoryBoundary
    true refl
    true refl
    false refl
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
  "The pinned Gauthey 940 x 668 selected-ROI-by-time matrix has a source-code-paid common conventional-2P protocol timebase and can feed a declared downstream PCA-3 candidate trajectory. The compact pooled export does not retain enough selection identity to map each selected row back to its exact source trial/plane/ROI. Protocol alignment therefore does not manufacture row identity, MaleCNS registration, promotion or causality."
