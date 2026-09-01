module DASHI.Cognition.PNF.SensibLawGWBv01ResidualFrontierCertificationV03Exact where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Exact operator-produced GWB v0.3 receipt on Rust PR #2 head 7c336418...
--
-- v0.3 preserves the v0.2 semantic observation identity and adds an exact
-- eight-way residual histogram.  The histogram is workflow/search evidence;
-- counts do not become semantic quality, truth, confidence or authority.
------------------------------------------------------------------------

record ResidualHistogram : Set where
  constructor residualHistogram
  field
    negationScopeUnresolved : Nat
    modalityScopeUnresolved : Nat
    temporalAnchorUnresolved : Nat
    conditionalScopeUnresolved : Nat
    clauseInterpretationAmbiguous : Nat
    referenceAttachmentUnresolved : Nat
    qualifierAttachmentUnresolved : Nat
    unsupportedDependency : Nat
    total : Nat

open ResidualHistogram public

record PassTiming : Set where
  constructor passTiming
  field
    parserOccupancyNs : Nat
    framingActiveNs : Nat
    directActiveNs : Nat
    referenceActiveNs : Nat
    pipelineWallNs : Nat
    controllerWallNs : Nat
    postParserTailNs : Nat

open PassTiming public

record ExpandedResidualFrontierReceipt : Set where
  constructor expandedResidualFrontierReceipt
  field
    rustHead : String
    schemaRef : String
    profileRef : String
    projectionManifestSha256 : String
    observationDigestSha256 : String
    observationBytes : Nat
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
    spacyModel : String
    spacyVersion : String
    spacyColdLoadNs : Nat
    parityTiming : PassTiming
    directTiming : PassTiming
    directOnlyRatioDecimal : String
    productionOnePointTwoTier : Bool
    directOnlyTwoXGatePassed : Bool
    observationDigestsMatched : Bool
    sameResidualFrontierAcrossPasses : Bool
    histogram : ResidualHistogram
    fullGatePassed : Bool

open ExpandedResidualFrontierReceipt public

canonicalResidualHistogramV03 : ResidualHistogram
canonicalResidualHistogramV03 =
  residualHistogram
    3902
    30807
    5699
    9356
    27618
    12223
    82647
    533994
    706246

parityTimingV03 : PassTiming
parityTimingV03 =
  passTiming
    146312110897
    1107080006
    107958330
    76412772
    157964167117
    157969730393
    5803246

directTimingV03 : PassTiming
directTimingV03 =
  passTiming
    137008017638
    1069610995
    107513967
    0
    148439241870
    148445308401
    6358287

expandedResidualFrontierV03 : ExpandedResidualFrontierReceipt
expandedResidualFrontierV03 =
  expandedResidualFrontierReceipt
    "7c3364186fffea3bc4853df504bf7163243697f6"
    "sensiblaw.gwb-expanded-semantic-certification-receipt.v0_3"
    "tranche-profile:gwb:v0_1"
    "b6c24ee502de49b8453af8ef02999bfc202ae10eb23f7837e802b291c386bd83"
    "994267e256e93776cea037fb0ad43834799c32dc4d28bfeecf438569fe387165"
    37469466
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
    "en_core_web_sm"
    "3.8.11"
    554068421
    parityTimingV03
    directTimingV03
    "1.0834347100926849"
    true
    true
    true
    true
    canonicalResidualHistogramV03
    true

parityCoversAllSentences :
  parityChecked expandedResidualFrontierV03 ≡ sentences expandedResidualFrontierV03
parityCoversAllSentences = refl

parityFailuresZero : parityFailed expandedResidualFrontierV03 ≡ 0
parityFailuresZero = refl

projectionFailuresZero : projectionFailures expandedResidualFrontierV03 ≡ 0
projectionFailuresZero = refl

publicationEffectsZero : publicationEffects expandedResidualFrontierV03 ≡ 0
publicationEffectsZero = refl

histogramTotalIsResidualTotal :
  total canonicalResidualHistogramV03 ≡ residuals expandedResidualFrontierV03
histogramTotalIsResidualTotal = refl

unsupportedDependencyIsDominantCoarseBucket :
  unsupportedDependency canonicalResidualHistogramV03 ≡ 533994
unsupportedDependencyIsDominantCoarseBucket = refl

fullV03GatePassed : fullGatePassed expandedResidualFrontierV03 ≡ true
fullV03GatePassed = refl

data ResidualCountIsSemanticQuality : Set where
data ResidualCountIsTruthConfidence : Set where
data GWBResidualHistogramIsUniversalLegalDistribution : Set where

residualCountIsNotSemanticQuality : ResidualCountIsSemanticQuality → ⊥
residualCountIsNotSemanticQuality ()

residualCountIsNotTruthConfidence : ResidualCountIsTruthConfidence → ⊥
residualCountIsNotTruthConfidence ()

gwbHistogramDoesNotUniversalize : GWBResidualHistogramIsUniversalLegalDistribution → ⊥
gwbHistogramDoesNotUniversalize ()
