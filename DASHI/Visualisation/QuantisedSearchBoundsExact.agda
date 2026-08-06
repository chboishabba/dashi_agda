module DASHI.Visualisation.QuantisedSearchBoundsExact where

open import DASHI.Core.Prelude

import DASHI.Visualisation.CoarseSliceSearchExact as Search

------------------------------------------------------------------------
-- Quantising preactivations and quantising post-activation values are distinct
-- approximation paths.  The concrete table prevents the stages being silently
-- interchanged.

data ScalarLevel : Set where
  levelZero : ScalarLevel
  levelOne : ScalarLevel
  levelTwo : ScalarLevel
  levelThree : ScalarLevel

data QuantisationStage : Set where
  quantisePreactivation : QuantisationStage
  quantiseActivation : QuantisationStage

preactivationQuantiser : ScalarLevel → ScalarLevel
preactivationQuantiser levelZero = levelZero
preactivationQuantiser levelOne = levelZero
preactivationQuantiser levelTwo = levelTwo
preactivationQuantiser levelThree = levelTwo

finiteActivation : ScalarLevel → ScalarLevel
finiteActivation levelZero = levelZero
finiteActivation levelOne = levelOne
finiteActivation levelTwo = levelThree
finiteActivation levelThree = levelThree

activationQuantiser : ScalarLevel → ScalarLevel
activationQuantiser levelZero = levelZero
activationQuantiser levelOne = levelOne
activationQuantiser levelTwo = levelTwo
activationQuantiser levelThree = levelTwo

quantisedPath : QuantisationStage → ScalarLevel → ScalarLevel
quantisedPath quantisePreactivation x =
  finiteActivation (preactivationQuantiser x)
quantisedPath quantiseActivation x =
  activationQuantiser (finiteActivation x)

quantisationStagesCanDiffer :
  quantisedPath quantisePreactivation levelOne
  ≡
  quantisedPath quantiseActivation levelOne
  →
  ⊥
quantisationStagesCanDiffer ()

------------------------------------------------------------------------
-- Saturation erases distinctions.  Storage range and accumulation range must
-- be tracked separately.

data ExtendedLevel : Set where
  withinRangeLow : ExtendedLevel
  withinRangeHigh : ExtendedLevel
  beyondRangeOne : ExtendedLevel
  beyondRangeTwo : ExtendedLevel

data StoredLevel : Set where
  storedLow : StoredLevel
  storedHigh : StoredLevel

clipToStorage : ExtendedLevel → StoredLevel
clipToStorage withinRangeLow = storedLow
clipToStorage withinRangeHigh = storedHigh
clipToStorage beyondRangeOne = storedHigh
clipToStorage beyondRangeTwo = storedHigh

clippingCollision :
  clipToStorage beyondRangeOne
  ≡
  clipToStorage beyondRangeTwo
clippingCollision = refl

extendedValuesRemainDistinct :
  beyondRangeOne ≡ beyondRangeTwo → ⊥
extendedValuesRemainDistinct ()

------------------------------------------------------------------------
-- Shared calibration and independent per-plane calibration define different
-- objectives.  Per-plane scaling can reverse the ranking.

data CalibrationScope : Set where
  sharedBatchCalibration : CalibrationScope
  independentPlaneCalibration : CalibrationScope

calibratedScore :
  CalibrationScope → Search.PlaneCandidate → Nat
calibratedScore sharedBatchCalibration Search.axisCandidate = 5
calibratedScore sharedBatchCalibration Search.broadAngledCandidate = 9
calibratedScore sharedBatchCalibration Search.compactIslandCandidate = 4
calibratedScore independentPlaneCalibration Search.axisCandidate = 5
calibratedScore independentPlaneCalibration Search.broadAngledCandidate = 6
calibratedScore independentPlaneCalibration Search.compactIslandCandidate = 10

sharedCalibrationWinner : Search.PlaneCandidate
sharedCalibrationWinner = Search.broadAngledCandidate

independentCalibrationWinner : Search.PlaneCandidate
independentCalibrationWinner = Search.compactIslandCandidate

calibrationChangesWinner :
  sharedCalibrationWinner ≡ independentCalibrationWinner → ⊥
calibrationChangesWinner ()

------------------------------------------------------------------------
-- Near-tie ordering can be destroyed by quantisation, while a sufficiently
-- separated pair retains its order.

data CandidatePair : Set where
  nearTiePair : CandidatePair
  stableMarginPair : CandidatePair

exactFirstScore : CandidatePair → Nat
exactFirstScore nearTiePair = 11
exactFirstScore stableMarginPair = 20

exactSecondScore : CandidatePair → Nat
exactSecondScore nearTiePair = 10
exactSecondScore stableMarginPair = 10

quantisedFirstScore : CandidatePair → Nat
quantisedFirstScore nearTiePair = 10
quantisedFirstScore stableMarginPair = 19

quantisedSecondScore : CandidatePair → Nat
quantisedSecondScore nearTiePair = 10
quantisedSecondScore stableMarginPair = 11

nearTieBecomesTie :
  quantisedFirstScore nearTiePair
  ≡
  quantisedSecondScore nearTiePair
nearTieBecomesTie = refl

stableMarginRemainsOrdered :
  quantisedFirstScore stableMarginPair
  ≡
  quantisedSecondScore stableMarginPair
  →
  ⊥
stableMarginRemainsOrdered ()

------------------------------------------------------------------------
-- Two opposite corners are not upper and lower bounds for a nonlinear cell.

data CellSample : Set where
  lowerCorner : CellSample
  upperCorner : CellSample
  interiorPeak : CellSample

nonlinearCellScore : CellSample → Nat
nonlinearCellScore lowerCorner = 2
nonlinearCellScore upperCorner = 3
nonlinearCellScore interiorPeak = 9

interiorExceedsBothOppositeCorners :
  nonlinearCellScore interiorPeak ≡ nonlinearCellScore upperCorner → ⊥
interiorExceedsBothOppositeCorners ()

------------------------------------------------------------------------
-- Integer-scaled Lipschitz cell interval.  The numbers represent one sample
-- score plus a declared L*r margin.

cellCentreScore : Nat
cellCentreScore = 12

lipschitzConstantScaled : Nat
lipschitzConstantScaled = 3

cellRadiusScaled : Nat
cellRadiusScaled = 2

lipschitzMarginScaled : Nat
lipschitzMarginScaled =
  lipschitzConstantScaled * cellRadiusScaled

cellUpperBoundScaled : Nat
cellUpperBoundScaled =
  cellCentreScore + lipschitzMarginScaled

cellUpperBoundIsEighteen :
  cellUpperBoundScaled ≡ 18
cellUpperBoundIsEighteen = refl

------------------------------------------------------------------------
-- Top-m proposal rather than winner-only trust.

data TopThreeProposal : Set where
  allThreeCandidates : TopThreeProposal

data Proposed : Search.PlaneCandidate → TopThreeProposal → Set where
  axisProposed : Proposed Search.axisCandidate allThreeCandidates
  broadProposed : Proposed Search.broadAngledCandidate allThreeCandidates
  compactProposed : Proposed Search.compactIslandCandidate allThreeCandidates

floatWinnerRetained :
  Proposed Search.floatWinner allThreeCandidates
floatWinnerRetained = broadProposed

record SearchConfiguration : Set where
  constructor searchConfiguration
  field
    storageBits : Nat
    accumulationBits : Nat
    sharedCalibration : Bool
    shortlistSize : Nat
    floatReranking : Bool

open SearchConfiguration public

canonicalSafeSearchConfiguration : SearchConfiguration
canonicalSafeSearchConfiguration =
  searchConfiguration 8 32 true 3 true

record CandidateDiagnostic : Set where
  constructor candidateDiagnostic
  field
    meanRawActivity : Nat
    activeCoverage : Nat
    classEntropy : Nat
    weightVariation : Nat
    saturationCount : Nat
    tieCount : Nat
    finalScore : Nat

open CandidateDiagnostic public

floatWinnerDiagnostic : CandidateDiagnostic
floatWinnerDiagnostic =
  candidateDiagnostic 10 9 8 8 0 1 79

quantisedIslandDiagnostic : CandidateDiagnostic
quantisedIslandDiagnostic =
  candidateDiagnostic 12 2 1 1 7 6 36

coverageDiagnosticSeparatesWinners :
  activeCoverage floatWinnerDiagnostic
  ≡
  activeCoverage quantisedIslandDiagnostic
  →
  ⊥
coverageDiagnosticSeparatesWinners ()

record QuantisedSearchBoundsBoundary : Set where
  constructor quantisedSearchBoundsBoundary
  field
    preactivationAndActivationQuantisationAreInterchangeable : Bool
    preactivationAndActivationQuantisationAreInterchangeableIsFalse :
      preactivationAndActivationQuantisationAreInterchangeable ≡ false

    clippingPreservesAllInputDistinctions : Bool
    clippingPreservesAllInputDistinctionsIsFalse :
      clippingPreservesAllInputDistinctions ≡ false

    perPlaneCalibrationPreservesCrossPlaneRanking : Bool
    perPlaneCalibrationPreservesCrossPlaneRankingIsFalse :
      perPlaneCalibrationPreservesCrossPlaneRanking ≡ false

    twoCornerSamplesAreNonlinearCellBounds : Bool
    twoCornerSamplesAreNonlinearCellBoundsIsFalse :
      twoCornerSamplesAreNonlinearCellBounds ≡ false

    winnerOnlyInt8SearchHasCertifiedRecall : Bool
    winnerOnlyInt8SearchHasCertifiedRecallIsFalse :
      winnerOnlyInt8SearchHasCertifiedRecall ≡ false

open QuantisedSearchBoundsBoundary public

canonicalQuantisedSearchBoundsBoundary :
  QuantisedSearchBoundsBoundary
canonicalQuantisedSearchBoundsBoundary =
  quantisedSearchBoundsBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
