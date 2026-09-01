module DASHI.Cognition.PNF.SensibLawGWBv01RuntimeCertificationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.DirectDeltaCompilerActivationExact as Activation
import DASHI.Cognition.PNF.RuntimeThroughputConstitution as Throughput

------------------------------------------------------------------------
-- Exact bounded runtime receipt for SensibLaw GWB v0.1.
--
-- This owner records the operator-produced full certification receipt from the
-- Rust direct-delta implementation.  It deliberately does not mutate the older
-- activation snapshot in DirectDeltaCompilerActivationExact: that module is a
-- historical pre-parity cut.  This module is the post-run current-state owner.
--
-- Timing units below are nanoseconds, exactly as emitted by the canonical
-- `sensiblaw.gwb-full-certification-receipt.v0_1` runtime receipt.
------------------------------------------------------------------------

data MeasuredPerformanceTier : Set where
  architectural2x production1_5x production1_2x : MeasuredPerformanceTier

record RuntimeTimingBreakdown : Set where
  constructor runtimeTimingBreakdown
  field
    spacyModelColdLoadNs : Nat
    spacyParserWallOccupancyNs : Nat
    sensibLawActiveNs : Nat
    totalSemanticPipelineWallNs : Nat
    externalControllerWallNs : Nat
    postParserTailNs : Nat

    -- Ratio is retained as the exact decimal receipt scaled by 10^16 rather
    -- than reconstructed from an unowned machine arithmetic theorem.
    parserRelativeRatioScaled : Nat
    parserRelativeRatioScale : Nat
    measuredTier : MeasuredPerformanceTier

open RuntimeTimingBreakdown public

record GWBv01CorpusIdentity : Set where
  constructor gwbV01CorpusIdentity
  field
    profileRef : String
    certifiedRustHead : String
    projectionManifestSha256 : String
    documentCount : Nat
    projectedBytes : Nat
    sentenceCount : Nat
    paragraphCount : Nat

open GWBv01CorpusIdentity public

record BoundedDirectReferenceParityReceipt : Set where
  constructor boundedDirectReferenceParityReceipt
  field
    corpus : GWBv01CorpusIdentity
    parityChecked : Nat
    parityFailed : Nat
    parityFailedZero : parityFailed ≡ 0
    parityCoversAllSentences : parityChecked ≡ sentenceCount corpus

open BoundedDirectReferenceParityReceipt public

record GWBv01RuntimeCertificationReceipt : Set where
  constructor gwbV01RuntimeCertificationReceipt
  field
    corpus : GWBv01CorpusIdentity
    parity : BoundedDirectReferenceParityReceipt
    timing : RuntimeTimingBreakdown

    candidateDeltas : Nat
    residuals : Nat
    symbols : Nat
    publishedGenerations : Nat
    publishedGenerationsZero : publishedGenerations ≡ 0
    rustReturnCode : Nat
    rustReturnCodeZero : rustReturnCode ≡ 0

    projectedHashesVerifiedBeforeTiming : Bool
    projectedHashesVerifiedBeforeTimingTrue :
      projectedHashesVerifiedBeforeTiming ≡ true
    projectedByteCountsVerifiedBeforeTiming : Bool
    projectedByteCountsVerifiedBeforeTimingTrue :
      projectedByteCountsVerifiedBeforeTiming ≡ true
    controllerAccountingMatched : Bool
    controllerAccountingMatchedTrue : controllerAccountingMatched ≡ true
    fullGatePassed : Bool
    fullGatePassedTrue : fullGatePassed ≡ true

open GWBv01RuntimeCertificationReceipt public

------------------------------------------------------------------------
-- Literal GWB v0.1 receipt.
------------------------------------------------------------------------

gwbV01Corpus : GWBv01CorpusIdentity
gwbV01Corpus =
  gwbV01CorpusIdentity
    "tranche-profile:gwb:v0_1"
    "60777f637732f28fed46458a30853d35b88a8a09"
    "b6c24ee502de49b8453af8ef02999bfc202ae10eb23f7837e802b291c386bd83"
    10
    4073000
    41044
    12742

gwbV01Timing : RuntimeTimingBreakdown
gwbV01Timing =
  runtimeTimingBreakdown
    701777110
    127919406353
    1135911693
    136058451205
    136067579483
    7611429
    10636263494652243
    10000000000000000
    production1_2x

gwbV01Parity : BoundedDirectReferenceParityReceipt
gwbV01Parity =
  boundedDirectReferenceParityReceipt
    gwbV01Corpus
    41044
    0
    refl
    refl

gwbV01CertifiedRun : GWBv01RuntimeCertificationReceipt
gwbV01CertifiedRun =
  gwbV01RuntimeCertificationReceipt
    gwbV01Corpus
    gwbV01Parity
    gwbV01Timing
    132006
    665838
    37610
    0
    refl
    0
    refl
    true refl
    true refl
    true refl
    true refl

------------------------------------------------------------------------
-- Current certification frontier.
--
-- G3 is now closed for this exact bounded corpus.  The old activation object's
-- `parityGate ≡ inactive` remains a historical pre-receipt fact; current status
-- is represented by possession of this bounded receipt, not by rewriting that
-- old object.
------------------------------------------------------------------------

data CurrentDirectFrontier : Set where
  boundedParityClosedAwaitingProductionCutover : CurrentDirectFrontier

currentDirectFrontier : CurrentDirectFrontier
currentDirectFrontier = boundedParityClosedAwaitingProductionCutover

boundedParityIsNowOwned : BoundedDirectReferenceParityReceipt
boundedParityIsNowOwned = parity gwbV01CertifiedRun

------------------------------------------------------------------------
-- Performance decomposition is not collapsed into one timing number.
--
-- In particular model cold-load and source projection are excluded from the
-- parser-relative semantic gate, while total semantic pipeline walltime still
-- includes the overlapping Rust streaming execution and shutdown tail.
------------------------------------------------------------------------

record TimingBoundary : Set where
  constructor timingBoundary
  field
    modelColdLoadIsSeparate : Bool
    modelColdLoadIsSeparateTrue : modelColdLoadIsSeparate ≡ true
    parserOccupancyIsSeparate : Bool
    parserOccupancyIsSeparateTrue : parserOccupancyIsSeparate ≡ true
    rustActiveIsSeparate : Bool
    rustActiveIsSeparateTrue : rustActiveIsSeparate ≡ true
    totalPipelineWallIsSeparate : Bool
    totalPipelineWallIsSeparateTrue : totalPipelineWallIsSeparate ≡ true
    postParserTailIsSeparate : Bool
    postParserTailIsSeparateTrue : postParserTailIsSeparate ≡ true

open TimingBoundary public

canonicalGWBTimingBoundary : TimingBoundary
canonicalGWBTimingBoundary =
  timingBoundary
    true refl
    true refl
    true refl
    true refl
    true refl

------------------------------------------------------------------------
-- Least-privilege non-generalisation.
------------------------------------------------------------------------

data SingleCorpusReceiptProvesUniversalParity : Set where

data SingleCorpusReceiptAuthorizesGlobalProductionCutover : Set where

data PerformanceTierPromotesSemanticTruth : Set where

singleCorpusDoesNotProveUniversalParity :
  SingleCorpusReceiptProvesUniversalParity → ⊥
singleCorpusDoesNotProveUniversalParity ()

singleCorpusDoesNotAuthorizeGlobalCutover :
  SingleCorpusReceiptAuthorizesGlobalProductionCutover → ⊥
singleCorpusDoesNotAuthorizeGlobalCutover ()

performanceTierStillHasNoSemanticAuthority :
  PerformanceTierPromotesSemanticTruth → ⊥
performanceTierStillHasNoSemanticAuthority ()

------------------------------------------------------------------------
-- Connection back to the generic runtime constitution.
------------------------------------------------------------------------

runtimePerformanceStillEmpirical :
  Throughput.runtimePerformanceMayPromoteSemanticTruth
    Throughput.canonicalRuntimeThroughputBoundary
  ≡ false
runtimePerformanceStillEmpirical = refl

historicalActivationSnapshotStillPreParity :
  Activation.parityGate Activation.sensibLawPackedDirectSeam
  ≡ Activation.inactive
historicalActivationSnapshotStillPreParity = refl
