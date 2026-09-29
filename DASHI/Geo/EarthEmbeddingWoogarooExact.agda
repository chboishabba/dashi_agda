module DASHI.Geo.EarthEmbeddingWoogarooExact where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool; true; false)

-- Earth-observation semantic carrier. Geometry, provenance and interpretation
-- must not be conflated. A model output is not a ground-truth measurement.
data Sensor : Set where
  sentinelOne sentinelTwo landsat lidar inSitu : Sensor

record Observation : Set where
  constructor observation
  field
    sensor : Sensor
    acquisitionYear : Nat
    spatialCell : String
    payloadReference : String
    qualityReference : String

record History : Set where
  constructor history
  field observationsReference : String
        spatialCell : String
        annualWindow : Nat
        sensorCoverageReference : String

data Model : Set where alphaEarth tessera tesseraV2 : Model

embeddingDimension : Model → Nat
embeddingDimension alphaEarth = 64
embeddingDimension tessera = 128
embeddingDimension tesseraV2 = 128

-- Coordinates remain opaque: 64 / 128 is per pixel and per annual window.
record Embedding (model : Model) : Set where
  constructor embedding
  field
    location : String
    year : Nat
    vectorReference : String
    version : String
    provenanceReference : String

record MatchedObservation (a b : Model) : Set where
  constructor matched
  field
    left : Embedding a
    right : Embedding b
    sameCell : Embedding.location left ≡ Embedding.location right
    sameWindow : Embedding.year left ≡ Embedding.year right

-- No spatial or temporal validation leakage is inferred by coincidence.
record HeldOutSplit : Set where
  constructor split
  field
    trainCells : String
    validationCells : String
    trainYears : String
    validationYears : String
    disjointnessReceipt : String

data EvidenceStage : Set where
  modelOutput calibratedObservation validatedPrediction
    ecologicalInterpretation legalConsumer : EvidenceStage

data HasEvidence : EvidenceStage → Set where
  produced : (source : String) → HasEvidence modelOutput
  calibrated : (source : String) → HasEvidence calibratedObservation
  validated : (model : String) → (holdout : HeldOutSplit) →
    (metricsReceipt : String) → HasEvidence validatedPrediction
  interpreted : (evidence : HasEvidence validatedPrediction) →
    (ecologyReceipt : String) → HasEvidence ecologicalInterpretation
  legallyReviewed : (evidence : HasEvidence ecologicalInterpretation) →
    (sourceInstrument : String) → (legalReview : String) →
    HasEvidence legalConsumer

-- There deliberately is NO constructor modelOutput → legalConsumer.
-- Matryoshka prefix lengths are representations, not accuracy theorems.
data Prefix : Set where d16 d32 d64 d128 : Prefix
prefixSize : Prefix → Nat
prefixSize d16 = 16
prefixSize d32 = 32
prefixSize d64 = 64
prefixSize d128 = 128

data Waterway : Set where
  springfieldLakes opossumCreek mountainCreek woogarooCreek
    brisbaneRiver : Waterway

data HydrologicConnection : Waterway → Waterway → Set where
  lakesToOpossum : HydrologicConnection springfieldLakes opossumCreek
  opossumToWoogaroo : HydrologicConnection opossumCreek woogarooCreek
  mountainToWoogaroo : HydrologicConnection mountainCreek woogarooCreek
  woogarooToBrisbane : HydrologicConnection woogarooCreek brisbaneRiver

data Downstream : Waterway → Waterway → Set where
  direct : ∀ {a b} → HydrologicConnection a b → Downstream a b
  trans : ∀ {a b c} → Downstream a b → Downstream b c → Downstream a c

springfieldToBrisbane : Downstream springfieldLakes brisbaneRiver
springfieldToBrisbane =
  trans (direct lakesToOpossum)
    (trans (direct opossumToWoogaroo) (direct woogarooToBrisbane))

-- Source refs name audit owners, not a direct physical measurement.
record WoogarooExperiment : Set where
  constructor experiment
  field
    selectedRegion : String
    baselineAttributes : String
    alphaEarthSamples : String
    tesseraSamples : String
    groundTruth : String
    splitPlan : HeldOutSplit
    measuredOutputs : String
    independentValidation : String

-- Separate landscape/canopy, water quality and legal downstream consumers;
-- legal validity is not a consequence of an embedding similarity score.
data CandidateTarget : Set where
  riparianChange canopyStructure runoff sediment waterQuality habitat : CandidateTarget

record CandidatePrediction : Set where
  constructor prediction
  field target : CandidateTarget
        experiment : WoogarooExperiment
        outputReceipt : String
        isValidated : Bool

sameWindowReflexive : ∀ {m} (v : Embedding m) →
  Embedding.year v ≡ Embedding.year v
sameWindowReflexive v = refl
