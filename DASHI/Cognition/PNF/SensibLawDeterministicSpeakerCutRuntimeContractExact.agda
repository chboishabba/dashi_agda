module DASHI.Cognition.PNF.SensibLawDeterministicSpeakerCutRuntimeContractExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Exact handoff for the Rust sidecar.
------------------------------------------------------------------------

record ScaledVaderObservation : Set where
  constructor scaledVaderObservation
  field
    negativeMilli : Nat
    neutralMilli : Nat
    positiveMilli : Nat
    compoundNegative : Bool
    compoundMagnitudeTenThousand : Nat
    producerReference : String
    sourceSpanReference : String

open ScaledVaderObservation public

record DeterministicCutFeatureReceipt : Set where
  constructor deterministicCutFeatureReceipt
  field
    sentenceId : Nat
    leftTokenCount : Nat
    rightTokenCount : Nat
    dependencyEdgesCrossing : Nat
    residualCount : Nat
    punctuationStrength : Nat
    discourseMarkerAtRight : Bool
    perspectiveShift : Bool
    compoundDeltaTenThousand : Nat
    leftProfileCandidate : String
    rightProfileCandidate : String
    profileEvidencePresent : Bool
    featureSchemaVersion : String
    candidateOnly : Bool

open DeterministicCutFeatureReceipt public

record RuntimeInputReceipt : Set where
  constructor runtimeInputReceipt
  field
    sourceReference : String
    sourceSha256Reference : String
    parserTsvReference : String
    pnfStdoutReference : String
    optionalProfileReference : String
    parserModelReference : String
    sentimentProducerReference : String

open RuntimeInputReceipt public

abcInputReceipt : RuntimeInputReceipt
abcInputReceipt = runtimeInputReceipt
  "9 Sept at 8-03 pm source transcript"
  "44ffc914cde420e597deeb79fc84e1c8d53eef98e338e2901ede587011bab3cc"
  "parser.tsv"
  "pnf.stdout"
  "optional held-out speaker profile TSV"
  "existing spaCy parse; exact installed en_core_web_sm version/digest to capture at run time"
  "vader_parity 0.1.0 / Python vaderSentiment 3.3.2 parity target"

record RuntimeCutBoundary : Set where
  constructor runtimeCutBoundary
  field
    lowDependencyCrossingMaySupportCut : Bool
    lowDependencyCrossingMaySupportCutIsTrue : lowDependencyCrossingMaySupportCut ≡ true
    vaderDeltaMaySupportCut : Bool
    vaderDeltaMaySupportCutIsTrue : vaderDeltaMaySupportCut ≡ true
    residualDensityMaySupportInspection : Bool
    residualDensityMaySupportInspectionIsTrue : residualDensityMaySupportInspection ≡ true
    anySingleFeatureProvesCut : Bool
    anySingleFeatureProvesCutIsFalse : anySingleFeatureProvesCut ≡ false
    cutScoreProvesSpeakerIdentity : Bool
    cutScoreProvesSpeakerIdentityIsFalse : cutScoreProvesSpeakerIdentity ≡ false
    profileScoreProvesSpeakerIdentity : Bool
    profileScoreProvesSpeakerIdentityIsFalse : profileScoreProvesSpeakerIdentity ≡ false

canonicalRuntimeCutBoundary : RuntimeCutBoundary
canonicalRuntimeCutBoundary = runtimeCutBoundary true refl true refl true refl false refl false refl false refl
