module DASHI.Biology.DrosophilaBenchmarkReceiptProtocol where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Biology.DrosophilaMaleCNSEffectorObservationBridge as Fly

------------------------------------------------------------------------
-- Dataset/run receipts for literal MaleCNS + registered functional + behaviour
-- experiments.  Stable scientific attribution and immutable artifact hashes are
-- separate provenance coordinates.
------------------------------------------------------------------------

data ArtifactRole : Set where
  structuralConnectomeArtifact : ArtifactRole
  functionalImagingArtifact : ArtifactRole
  registrationMapArtifact : ArtifactRole
  behaviourArtifact : ArtifactRole
  splitArtifact : ArtifactRole
  predictorOutputArtifact : ArtifactRole

data ReceiptBoundary : Set where
  noUnhashedDatasetPromotion : ReceiptBoundary
  noVersionlessDatasetPromotion : ReceiptBoundary
  noRegistrationWithoutInputHashes : ReceiptBoundary
  noTrainHeldOutLeakage : ReceiptBoundary
  noMetricWithoutOutputHash : ReceiptBoundary
  noRunWithoutPredictorCommit : ReceiptBoundary

record ArtifactReceipt : Set where
  field
    role : ArtifactRole
    artifactName : String
    sha256 : String
    datasetVersion : String
    source : Fly.ScientificSourceReceipt

open ArtifactReceipt public

record RegistrationReceipt : Set where
  field
    structuralArtifact : ArtifactReceipt
    functionalArtifact : ArtifactReceipt
    mappingArtifact : ArtifactReceipt
    methodSource : Fly.ScientificSourceReceipt
    evidenceKind : String
    residualDefinition : String

    structuralHash : String
    functionalHash : String
    mappingHash : String

    registrationInputsPinned : Bool
    registrationInputsPinnedIsTrue :
      registrationInputsPinned ≡ true

open RegistrationReceipt public

record BenchmarkSplitReceipt : Set where
  field
    splitArtifactReceipt : ArtifactReceipt
    trainIDsHash : String
    heldOutIDsHash : String
    leakageCheckPassed : Bool
    leakageCheckPassedIsTrue :
      leakageCheckPassed ≡ true

open BenchmarkSplitReceipt public

record BenchmarkRunReceipt : Set where
  field
    structuralReceipt : ArtifactReceipt
    functionalReceipt : ArtifactReceipt
    behaviourReceipt : ArtifactReceipt
    registrationReceipt : RegistrationReceipt
    splitReceipt : BenchmarkSplitReceipt

    predictorName : String
    predictorCommit : String
    outputHash : String
    metricName : String
    metricValueReading : String

    exactInputHashesPinned : Bool
    exactInputHashesPinnedIsTrue :
      exactInputHashesPinned ≡ true

    outputHashPinned : Bool
    outputHashPinnedIsTrue :
      outputHashPinned ≡ true

    predictorCommitPinned : Bool
    predictorCommitPinnedIsTrue :
      predictorCommitPinned ≡ true

open BenchmarkRunReceipt public

canonicalReceiptBoundaries : List ReceiptBoundary
canonicalReceiptBoundaries =
  noUnhashedDatasetPromotion
  ∷ noVersionlessDatasetPromotion
  ∷ noRegistrationWithoutInputHashes
  ∷ noTrainHeldOutLeakage
  ∷ noMetricWithoutOutputHash
  ∷ noRunWithoutPredictorCommit
  ∷ []
