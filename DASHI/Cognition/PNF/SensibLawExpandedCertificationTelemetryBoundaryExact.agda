module DASHI.Cognition.PNF.SensibLawExpandedCertificationTelemetryBoundaryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Post-software-validation expanded GWB run on Rust head 0833fb4...
--
-- The run established expanded direct/reference semantic parity and retained
-- candidate/residual/alternative accounting, but the first strict two-pass
-- certification schema also hashed M\tspacy_parse_ns=... runtime telemetry.
-- Since that telemetry intentionally varies between passes, equal semantic
-- parser observations need not produce equal raw frame-stream hashes.
--
-- This owner preserves that failed strict-hash attempt as a negative receipt;
-- it does not rewrite it into a successful full-certification claim.
------------------------------------------------------------------------

record ExpandedRunPositiveSurface : Set where
  constructor expandedRunPositiveSurface
  field
    rustHead : String
    sentences : Nat
    parityChecked : Nat
    parityFailed : Nat
    candidates : Nat
    residuals : Nat
    alternatives : Nat
    projectionFailures : Nat
    publicationEffects : Nat
    directOnlyRatioTenThousandths : Nat
    productionOnePointTwoTier : Bool
    directOnlyTwoXGatePassed : Bool

open ExpandedRunPositiveSurface public

expandedRun0833 : ExpandedRunPositiveSurface
expandedRun0833 =
  expandedRunPositiveSurface
    "0833fb4b56a63ee5f9780ad355949b7352b54f25"
    41044
    41044
    0
    236232
    706246
    27618
    0
    0
    10644
    true
    true

expandedParityCoversAllSentences :
  parityChecked expandedRun0833 ≡ sentences expandedRun0833
expandedParityCoversAllSentences = refl

expandedParityFailureCountZero : parityFailed expandedRun0833 ≡ 0
expandedParityFailureCountZero = refl

expandedProjectionFailureCountZero : projectionFailures expandedRun0833 ≡ 0
expandedProjectionFailureCountZero = refl

expandedPublicationEffectsZero : publicationEffects expandedRun0833 ≡ 0
expandedPublicationEffectsZero = refl

------------------------------------------------------------------------
-- Timing observations reported with the failed strict-hash run.
-- These are retained as reported pass/active timings only; no stronger
-- identification is inferred beyond the labels supplied by the runtime report.
------------------------------------------------------------------------

record ExpandedTimingObservation : Set where
  constructor expandedTimingObservation
  field
    spacyColdLoadNs : Nat
    parityPassReportedNs : Nat
    parityFramingActiveNs : Nat
    parityDirectActiveNs : Nat
    parityReferenceActiveNs : Nat
    directOnlyPassReportedNs : Nat
    directOnlyFramingActiveNs : Nat
    directOnlyDirectActiveNs : Nat

expandedTiming0833 : ExpandedTimingObservation
expandedTiming0833 =
  expandedTimingObservation
    560216379
    112007364664
    748880884
    77293897
    61865524
    108627304808
    777343742
    83259598

------------------------------------------------------------------------
-- Raw-stream hash negative receipt.
------------------------------------------------------------------------

record RawStreamHashFailureReceipt : Set where
  constructor rawStreamHashFailureReceipt
  field
    parityRawHashPrefix : String
    directRawHashPrefix : String
    parityRawBytes : Nat
    directRawBytes : Nat
    equalByteCount : parityRawBytes ≡ directRawBytes
    rawHashesMatched : Bool

rawHashFailure0833 : RawStreamHashFailureReceipt
rawHashFailure0833 =
  rawStreamHashFailureReceipt
    "a66ba29e"
    "8bfec146"
    37469744
    37469744
    refl
    false

------------------------------------------------------------------------
-- Correct observation-language split.
------------------------------------------------------------------------

data StreamFrameClass : Set where
  documentFrame paragraphOpenFrame sentenceFrame tokenFrame sentenceEndFrame
  paragraphEndFrame runtimeTimingTelemetryFrame : StreamFrameClass

semanticObservationFrame : StreamFrameClass → Bool
semanticObservationFrame documentFrame = true
semanticObservationFrame paragraphOpenFrame = true
semanticObservationFrame sentenceFrame = true
semanticObservationFrame tokenFrame = true
semanticObservationFrame sentenceEndFrame = true
semanticObservationFrame paragraphEndFrame = true
semanticObservationFrame runtimeTimingTelemetryFrame = false

runtimeTimingTelemetryIsNotSemanticObservation :
  semanticObservationFrame runtimeTimingTelemetryFrame ≡ false
runtimeTimingTelemetryIsNotSemanticObservation = refl

record CanonicalExpandedObservationDigestPolicy : Set where
  constructor canonicalExpandedObservationDigestPolicy
  field
    includesDocumentParagraphSentenceTokenFrames : Bool
    excludesRuntimeTimingTelemetry : Bool
    controlFramesAreNotSemanticObservation : Bool

canonicalExpandedObservationDigestPolicy : CanonicalExpandedObservationDigestPolicy
canonicalExpandedObservationDigestPolicy =
  canonicalExpandedObservationDigestPolicy true true true

------------------------------------------------------------------------
-- Hard boundaries.
------------------------------------------------------------------------

data RawStreamHashMismatchRefutesExpandedSemanticParity : Set where
data RuntimeTelemetryBelongsToSemanticObservationIdentity : Set where
data FailedV01RawHashMeansExpandedPerformanceFailed : Set where

data V01RawHashFailureAlreadyProvesV02CanonicalDigest : Set where

rawHashMismatchDoesNotRefuteExpandedSemanticParity :
  RawStreamHashMismatchRefutesExpandedSemanticParity → ⊥
rawHashMismatchDoesNotRefuteExpandedSemanticParity ()

runtimeTelemetryDoesNotBelongToSemanticObservationIdentity :
  RuntimeTelemetryBelongsToSemanticObservationIdentity → ⊥
runtimeTelemetryDoesNotBelongToSemanticObservationIdentity ()

rawHashFailureDoesNotMeanExpandedPerformanceFailed :
  FailedV01RawHashMeansExpandedPerformanceFailed → ⊥
rawHashFailureDoesNotMeanExpandedPerformanceFailed ()

v01FailureDoesNotPreCertifyCorrectedV02 :
  V01RawHashFailureAlreadyProvesV02CanonicalDigest → ⊥
v01FailureDoesNotPreCertifyCorrectedV02 ()

------------------------------------------------------------------------
-- Current frontier: rerun corrected canonical observation digest.
------------------------------------------------------------------------

data ExpandedCertificationFrontier : Set where
  semanticParityAndPerformanceObservedAwaitingCanonicalDigestRerun
  : ExpandedCertificationFrontier

currentExpandedCertificationFrontier : ExpandedCertificationFrontier
currentExpandedCertificationFrontier =
  semanticParityAndPerformanceObservedAwaitingCanonicalDigestRerun
