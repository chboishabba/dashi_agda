module DASHI.Biology.PsychogeographicHexagramObservationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Vec using (Vec) renaming ([] to vnil; _∷_ to _vcons_)

import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Biology.DASHIYijingTernaryDivinationExact as Yijing
import DASHI.Biology.DASHIYijingRelationalOperatorsExact as Relational
import DASHI.Biology.PsychogeographicFieldExact as Field

------------------------------------------------------------------------
-- A hexagram is a context-indexed coarse observation of a lived spatial
-- situation.  It is not an intrinsic label permanently attached to a street.
------------------------------------------------------------------------

scaleAt : Relational.LinePosition → Field.SpatialScale
scaleAt Relational.lineOne = Field.bodyFootingScale
scaleAt Relational.lineTwo = Field.intimateLocalityScale
scaleAt Relational.lineThree = Field.streetThresholdScale
scaleAt Relational.lineFour = Field.civicInterfaceScale
scaleAt Relational.lineFive = Field.districtOrganisationScale
scaleAt Relational.lineSix = Field.historicalHorizonScale

record HexagramObservationContext : Set where
  constructor hexagramObservationContext
  field
    signView : Yijing.SignView
    siteLabel : String
    timeIndex : Nat
    observerLabel : String
    authorityLabel : String

open HexagramObservationContext public

data LocalMicrostate : Set where
  sameHexDifferentPathA : LocalMicrostate
  sameHexDifferentPathB : LocalMicrostate
  transformedMicrostate : LocalMicrostate

coarseHexagram : LocalMicrostate → Yijing.TernaryHexagram
coarseHexagram sameHexDifferentPathA = Yijing.canonicalTernaryHexagram
coarseHexagram sameHexDifferentPathB = Yijing.canonicalTernaryHexagram
coarseHexagram transformedMicrostate = Yijing.canonicalResultingHexagram

hiddenPathCode : LocalMicrostate → Nat
hiddenPathCode sameHexDifferentPathA = 1
hiddenPathCode sameHexDifferentPathB = 2
hiddenPathCode transformedMicrostate = 3

projectionLosesPathInformation :
  coarseHexagram sameHexDifferentPathA
  ≡ coarseHexagram sameHexDifferentPathB
projectionLosesPathInformation = refl

microstatesRemainDistinctDespiteSameHexagram :
  ¬ (sameHexDifferentPathA ≡ sameHexDifferentPathB)
microstatesRemainDistinctDespiteSameHexagram ()

firstTrit : Yijing.TernaryHexagram → Triadic.KernelTrit
firstTrit (a vcons b vcons c vcons d vcons e vcons f vcons vnil) = a

observeFirstLine :
  HexagramObservationContext → LocalMicrostate → Yijing.YinYangObservation
observeFirstLine context state =
  Yijing.observeYinYang (signView context) (firstTrit (coarseHexagram state))

directContext : HexagramObservationContext
directContext =
  hexagramObservationContext Yijing.directView "church threshold" 3
    "walker" "structural/associative only"

reversedContext : HexagramObservationContext
reversedContext =
  hexagramObservationContext Yijing.reversedView "church threshold" 3
    "co-witness" "structural/associative only"

sameStateDirectlyReadsYin :
  observeFirstLine directContext sameHexDifferentPathA
  ≡ Yijing.yinObservation
sameStateDirectlyReadsYin = refl

sameStateReversedReadsYang :
  observeFirstLine reversedContext sameHexDifferentPathA
  ≡ Yijing.yangObservation
sameStateReversedReadsYang = refl

------------------------------------------------------------------------
-- Every line reading carries its scale, context, evidence lane and authority;
-- the bare trit does not determine a psychological or moral interpretation.
------------------------------------------------------------------------

data LineEvidence : Set where
  sensoryEvidence : LineEvidence
  memoryEvidence : LineEvidence
  socialEvidence : LineEvidence
  historicalEvidence : LineEvidence
  associativeEvidence : LineEvidence

record TypedLineReading : Set where
  constructor typedLineReading
  field
    linePosition : Relational.LinePosition
    spatialScale : Field.SpatialScale
    observedTrit : Triadic.KernelTrit
    observationContext : HexagramObservationContext
    evidence : LineEvidence
    readingAuthority : Yijing.ReadingAuthority

open TypedLineReading public

lineReadingAt :
  HexagramObservationContext →
  Relational.LinePosition →
  LineEvidence →
  Yijing.ReadingAuthority →
  LocalMicrostate →
  TypedLineReading
lineReadingAt context position evidenceLane authority state =
  typedLineReading
    position
    (scaleAt position)
    (Relational.lineAt position (coarseHexagram state))
    context
    evidenceLane
    authority

canonicalThresholdLineReading : TypedLineReading
canonicalThresholdLineReading =
  lineReadingAt directContext Relational.lineThree memoryEvidence
    Yijing.associativeAuthority sameHexDifferentPathA

canonicalThresholdReadingScaleIsStreet :
  spatialScale canonicalThresholdLineReading ≡ Field.streetThresholdScale
canonicalThresholdReadingScaleIsStreet = refl

canonicalThresholdReadingAuthorityIsAssociative :
  readingAuthority canonicalThresholdLineReading ≡ Yijing.associativeAuthority
canonicalThresholdReadingAuthorityIsAssociative = refl

------------------------------------------------------------------------
-- The received trigram images become bounded attention prompts.  The mapping
-- is interpretive and does not identify the place with the trigram image.
------------------------------------------------------------------------

data EnvironmentalPrompt : Set where
  authorityExposurePrompt : EnvironmentalPrompt
  groundSupportPrompt : EnvironmentalPrompt
  disruptionPrompt : EnvironmentalPrompt
  diffusionPrompt : EnvironmentalPrompt
  channelDangerPrompt : EnvironmentalPrompt
  visibilityPrompt : EnvironmentalPrompt
  boundaryStillnessPrompt : EnvironmentalPrompt
  gatheringExchangePrompt : EnvironmentalPrompt

promptFromImage : Relational.TrigramImage → EnvironmentalPrompt
promptFromImage Relational.heavenImage = authorityExposurePrompt
promptFromImage Relational.earthImage = groundSupportPrompt
promptFromImage Relational.thunderImage = disruptionPrompt
promptFromImage Relational.windWoodImage = diffusionPrompt
promptFromImage Relational.waterImage = channelDangerPrompt
promptFromImage Relational.fireImage = visibilityPrompt
promptFromImage Relational.mountainImage = boundaryStillnessPrompt
promptFromImage Relational.lakeMarshImage = gatheringExchangePrompt

lowerLocalTrigram : LocalMicrostate → Yijing.TernaryTrigram
lowerLocalTrigram state = Relational.lowerTrigram (coarseHexagram state)

upperGoverningTrigram : LocalMicrostate → Yijing.TernaryTrigram
upperGoverningTrigram state = Relational.upperTrigram (coarseHexagram state)

splitRecombinesPsychogeographicObservation :
  (state : LocalMicrostate) →
  Relational.composeTrigrams
    (lowerLocalTrigram state)
    (upperGoverningTrigram state)
  ≡ coarseHexagram state
splitRecombinesPsychogeographicObservation state =
  Relational.splitThenCompose (coarseHexagram state)

------------------------------------------------------------------------
-- Difference between anticipated and encountered readings.
------------------------------------------------------------------------

boolWeight : Bool → Nat
boolWeight false = 0
boolWeight true = 1

tritDifferent : Triadic.KernelTrit → Triadic.KernelTrit → Bool
tritDifferent Triadic.negativeTrit Triadic.negativeTrit = false
tritDifferent Triadic.zeroTrit Triadic.zeroTrit = false
tritDifferent Triadic.positiveTrit Triadic.positiveTrit = false
tritDifferent x y = true

hexagramDifference : Yijing.TernaryHexagram → Yijing.TernaryHexagram → Nat
hexagramDifference
  (a vcons b vcons c vcons d vcons e vcons f vcons vnil)
  (a' vcons b' vcons c' vcons d' vcons e' vcons f' vcons vnil) =
  boolWeight (tritDifferent a a')
  + boolWeight (tritDifferent b b')
  + boolWeight (tritDifferent c c')
  + boolWeight (tritDifferent d d')
  + boolWeight (tritDifferent e e')
  + boolWeight (tritDifferent f f')

canonicalAnticipatedEncounteredDifferenceIsTwo :
  hexagramDifference
    Yijing.canonicalTernaryHexagram
    Yijing.canonicalResultingHexagram
  ≡ 2
canonicalAnticipatedEncounteredDifferenceIsTwo = refl

record PsychogeographicHexagramBoundary : Set where
  constructor psychogeographicHexagramBoundary
  field
    hexagramIsObjectivePermanentSiteLabel : Bool
    hexagramIsObjectivePermanentSiteLabelIsFalse :
      hexagramIsObjectivePermanentSiteLabel ≡ false
    sameHexagramReconstructsHiddenPath : Bool
    sameHexagramReconstructsHiddenPathIsFalse :
      sameHexagramReconstructsHiddenPath ≡ false
    lowerUpperSplitIsInvariantPsychologicalDecomposition : Bool
    lowerUpperSplitIsInvariantPsychologicalDecompositionIsFalse :
      lowerUpperSplitIsInvariantPsychologicalDecomposition ≡ false
    trigramPromptIsPhysicalLaw : Bool
    trigramPromptIsPhysicalLawIsFalse : trigramPromptIsPhysicalLaw ≡ false

canonicalPsychogeographicHexagramBoundary : PsychogeographicHexagramBoundary
canonicalPsychogeographicHexagramBoundary =
  psychogeographicHexagramBoundary false refl false refl false refl false refl
