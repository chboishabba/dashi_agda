module DASHI.Cognition.PNF.SensibLawGWBv01ExpandedSemanticCertificationV02Exact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Exact bounded v0.2 expanded-semantic certification receipt.
--
-- This owner records the successful operator-produced GWB v0.1 expanded
-- semantic certification after the v0.1 raw-stream identity bug was corrected.
-- Semantic observation identity hashes D/P/S/T/E/Q only; M timing telemetry is
-- measured separately and explicitly excluded from the observation digest.
------------------------------------------------------------------------

record CanonicalObservationIdentity : Set where
  constructor canonicalObservationIdentity
  field
    digestSha256 : String
    observationBytes : Nat
    includedDPSTEQ : Bool
    excludedRuntimeTelemetryM : Bool
    parityAndDirectDigestsMatched : Bool

open CanonicalObservationIdentity public

record ExpandedSemanticSurfaceReceipt : Set where
  constructor expandedSemanticSurfaceReceipt
  field
    documents : Nat
    projectedBytes : Nat
    sentences : Nat
    paragraphs : Nat
    parityChecked : Nat
    parityFailed : Nat
    candidates : Nat
    residuals : Nat
    alternatives : Nat
    projectionFailures : Nat
    publicationEffects : Nat
    symbols : Nat
    canonicalObservation : CanonicalObservationIdentity

open ExpandedSemanticSurfaceReceipt public

record ExpandedPassTiming : Set where
  constructor expandedPassTiming
  field
    parserOccupancyNs : Nat
    framingActiveNs : Nat
    directActiveNs : Nat
    referenceActiveNs : Nat
    pipelineWallNs : Nat
    controllerWallNs : Nat
    postParserTailNs : Nat

open ExpandedPassTiming public

record ExpandedV02CertificationReceipt : Set where
  constructor expandedV02CertificationReceipt
  field
    schemaRef : String
    profileRef : String
    projectionManifestSha256 : String
    spacyModel : String
    spacyVersion : String
    spacyColdLoadNs : Nat
    surface : ExpandedSemanticSurfaceReceipt
    parityTiming : ExpandedPassTiming
    directOnlyTiming : ExpandedPassTiming
    directOnlyRatioScaled : Nat
    directOnlyRatioScale : Nat
    productionOnePointTwoTier : Bool
    directOnlyTwoXGatePassed : Bool
    sameDirectAccountingAcrossPasses : Bool
    referenceCostExcludedFromProductionSpeedClaim : Bool
    fullExpandedGatePassed : Bool

open ExpandedV02CertificationReceipt public

canonicalObservationV02 : CanonicalObservationIdentity
canonicalObservationV02 =
  canonicalObservationIdentity
    "994267e256e93776cea037fb0ad43834799c32dc4d28bfeecf438569fe387165"
    37469466
    true
    true
    true

expandedSurfaceV02 : ExpandedSemanticSurfaceReceipt
expandedSurfaceV02 =
  expandedSemanticSurfaceReceipt
    10
    4073000
    41044
    12742
    41044
    0
    236232
    706246
    27618
    0
    0
    37610
    canonicalObservationV02

parityPassTimingV02 : ExpandedPassTiming
parityPassTimingV02 =
  expandedPassTiming
    105271710744
    747440026
    78493205
    62553415
    112168176415
    112171472849
    2835271

directOnlyPassTimingV02 : ExpandedPassTiming
directOnlyPassTimingV02 =
  expandedPassTiming
    98390474132
    738796735
    80159250
    0
    105107239044
    105111075332
    3378806

expandedGWBv02CertifiedRun : ExpandedV02CertificationReceipt
expandedGWBv02CertifiedRun =
  expandedV02CertificationReceipt
    "sensiblaw.gwb-expanded-semantic-certification-receipt.v0_2"
    "tranche-profile:gwb:v0_1"
    "b6c24ee502de49b8453af8ef02999bfc202ae10eb23f7837e802b291c386bd83"
    "en_core_web_sm"
    "3.8.11"
    524989758
    expandedSurfaceV02
    parityPassTimingV02
    directOnlyPassTimingV02
    10682664147241412
    10000000000000000
    true
    true
    true
    true
    true

------------------------------------------------------------------------
-- Direct proof-relevant consequences of the literal receipt.
------------------------------------------------------------------------

expandedParityCoversAllSentences :
  parityChecked expandedSurfaceV02 ≡ sentences expandedSurfaceV02
expandedParityCoversAllSentences = refl

expandedParityFailuresZero : parityFailed expandedSurfaceV02 ≡ 0
expandedParityFailuresZero = refl

expandedProjectionFailuresZero : projectionFailures expandedSurfaceV02 ≡ 0
expandedProjectionFailuresZero = refl

expandedPublicationEffectsZero : publicationEffects expandedSurfaceV02 ≡ 0
expandedPublicationEffectsZero = refl

canonicalObservationDigestMatchesAcrossPasses :
  parityAndDirectDigestsMatched canonicalObservationV02 ≡ true
canonicalObservationDigestMatchesAcrossPasses = refl

runtimeTelemetryExcludedFromObservationIdentity :
  excludedRuntimeTelemetryM canonicalObservationV02 ≡ true
runtimeTelemetryExcludedFromObservationIdentity = refl

fullExpandedGateIsPassed :
  fullExpandedGatePassed expandedGWBv02CertifiedRun ≡ true
fullExpandedGateIsPassed = refl

------------------------------------------------------------------------
-- Current frontier and hard non-generalisation.
------------------------------------------------------------------------

data ExpandedSemanticCertificationFrontier : Set where
  boundedExpandedGWBv02CertifiedAwaitingAdmissionAndMultiCorpus
    : ExpandedSemanticCertificationFrontier

currentExpandedSemanticCertificationFrontier : ExpandedSemanticCertificationFrontier
currentExpandedSemanticCertificationFrontier =
  boundedExpandedGWBv02CertifiedAwaitingAdmissionAndMultiCorpus

data SingleExpandedCorpusProvesUniversalSemanticCorrectness : Set where
data ExpandedParityAutomaticallyAuthorizesPublication : Set where
data ExpandedGWBPerformanceProvesUniversalOnePointTwoTier : Set where
\data CandidateResidualCountsAreSemanticQualityScores : Set where

singleExpandedCorpusDoesNotProveUniversalSemanticCorrectness :
  SingleExpandedCorpusProvesUniversalSemanticCorrectness → ⊥
singleExpandedCorpusDoesNotProveUniversalSemanticCorrectness ()

expandedParityDoesNotAuthorizePublication :
  ExpandedParityAutomaticallyAuthorizesPublication → ⊥
expandedParityDoesNotAuthorizePublication ()

expandedGWBPerformanceDoesNotProveUniversalOnePointTwoTier :
  ExpandedGWBPerformanceProvesUniversalOnePointTwoTier → ⊥
expandedGWBPerformanceDoesNotProveUniversalOnePointTwoTier ()

candidateResidualCountsAreNotSemanticQualityScores :
  CandidateResidualCountsAreSemanticQualityScores → ⊥
candidateResidualCountsAreNotSemanticQualityScores ()
