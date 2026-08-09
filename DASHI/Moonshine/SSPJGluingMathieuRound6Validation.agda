module DASHI.Moonshine.SSPJGluingMathieuRound6Validation where

open import DASHI.Core.Prelude
open import Data.Rational.Base using (0ℚ)

import DASHI.Biology.EisensteinNineRingInterferenceExact as Eisenstein
import DASHI.Biology.EisensteinThreeSixSymmetryExact as ThreeSix
import DASHI.Biology.HalfChartNineRingQuotientExact as Half
import DASHI.Biology.IndexedJExternalGluingExact as Gluing
import DASHI.Biology.IteratedPointedAttachmentSpiralExact as Spiral
import DASHI.Moonshine.MathieuDivisorLatticeExact as Divisor
import DASHI.Moonshine.MathieuDivisorPathInterferenceExact as Path
import DASHI.Moonshine.MathieuJTransportIntegrationExact as Integration
import DASHI.Moonshine.MathieuStabilizerTowerExact as Mathieu
import DASHI.Moonshine.Monster196884FibreInterferenceExact as Monster

validationZeroOneSeam : Gluing.closeLinearTen Gluing.l1 ≡ Gluing.r0
validationZeroOneSeam = Gluing.zeroAndOneShareSeam

validationOneTenSeam :
  Gluing.closeLinearTen Gluing.l1 ≡ Gluing.closeLinearTen Gluing.l10
validationOneTenSeam = Gluing.oneAndTenCloseToSameSeam

validationTransportedIndex :
  Gluing.representationIndex Gluing.transportedTen
  ≡ Gluing.representationIndex Gluing.localOne + Gluing.hostTransportWidth
validationTransportedIndex = Gluing.transportedIndexLaw

validationJoinedEleven : Gluing.joinedAddressIndex ≡ 11
validationJoinedEleven = Gluing.joinedAddressIndexIsEleven

validationHalfChartTen : Half.unfoldedCount ≡ 10
validationHalfChartTen = Half.unfoldedCountIsTen

validationHalfChartNine : Half.quotientCount ≡ 9
validationHalfChartNine = Half.quotientCountIsNine

validationTernaryField : Eisenstein.nineAddressFieldCount ≡ 19683
validationTernaryField = Eisenstein.nineAddressFieldCountIs19683

validationLocalSymmetry : Eisenstein.localPhaseSymmetryCount ≡ 6
validationLocalSymmetry = Eisenstein.localPhaseSymmetryCountIsSix

validationThreePhaseCancellationReal :
  Eisenstein.realCoordinate Eisenstein.threePhaseSum ≡ 0ℚ
validationThreePhaseCancellationReal = Eisenstein.threePhaseCancellationReal

validationThreePhaseCycle :
  (phase : ThreeSix.TernaryPhase) →
  ThreeSix.nextPhase
    (ThreeSix.nextPhase
      (ThreeSix.nextPhase phase))
  ≡ phase
validationThreePhaseCycle = ThreeSix.threePhaseCycleCloses

validationSixEisensteinUnits : ThreeSix.eisensteinUnitCount ≡ 6
validationSixEisensteinUnits = ThreeSix.eisensteinUnitCountIsSix

validationMonsterSplit : Monster.fibreInterferenceTotal ≡ 196884
validationMonsterSplit = Monster.fibreInterferenceTotalIs196884

validationMonsterCoarseTrace :
  Monster.coarseSectorDimension ≡ 54
validationMonsterCoarseTrace = Monster.coarseSectorDimensionIs54

validationM11SharpFourOrder :
  Mathieu.groupOrder Mathieu.m11SharpFourOrderWitness
  ≡ 11 * 10 * 9 * 8
validationM11SharpFourOrder = Mathieu.m11OrderFromSharpFourTransitivity

validationM12SharpFiveOrder :
  Mathieu.groupOrder Mathieu.m12SharpFiveOrderWitness
  ≡ 12 * 11 * 10 * 9 * 8
validationM12SharpFiveOrder = Mathieu.m12OrderFromSharpFiveTransitivity

validationM11ThreePointStabilizerOrder :
  Mathieu.threePointStabilizerOrderInM11 ≡ 8
validationM11ThreePointStabilizerOrder =
  Mathieu.threePointStabilizerOrderInM11IsEight

validationMathieuEightNotD4Source :
  Mathieu.mathieuEightSource ≡ Mathieu.squareGridDihedralOrder → ⊥
validationMathieuEightNotD4Source = Mathieu.mathieuEightDoesNotComeFromD4

validationM12DivisorNodes : Divisor.nodeCount Divisor.m12Bounds ≡ 112
validationM12DivisorNodes = Divisor.m12DivisorNodeCount

validationM11DivisorNodes : Divisor.nodeCount Divisor.m11Bounds ≡ 60
validationM11DivisorNodes = Divisor.m11DivisorNodeCount

validationCentralizerClassSplit :
  Divisor.centralizerOrder * Divisor.classIndex ≡ 95040
validationCentralizerClassSplit = Divisor.centralizerTimesClassIndex

validationChooseTwelveFour : Divisor.choose 12 4 ≡ 495
validationChooseTwelveFour = Divisor.chooseTwelveFourIs495

validationPrimePathConfluence :
  Divisor.endpoint Divisor.historyTwoThree
  ≡ Divisor.endpoint Divisor.historyThreeTwo
validationPrimePathConfluence = Divisor.historiesShareEndpoint

validationDecoratedPathsReachSix :
  Divisor.endpoint
    (Path.leftHistory (Path.confluence Path.canonicalPhaseDecoratedConfluence))
  ≡ 6
validationDecoratedPathsReachSix = Path.canonicalHistoriesReachSix

validationDecoratedPathNodeIntensity :
  Path.nodeIntensity Path.canonicalPhaseDecoratedConfluence
  ≡ Eisenstein.qOne
validationDecoratedPathNodeIntensity = Path.canonicalNodeIntensityIsOne

validationDecoratedPathCrossTerm :
  Path.pathCrossTerm Path.canonicalPhaseDecoratedConfluence
  ≡ Eisenstein.qMinusOne
validationDecoratedPathCrossTerm = Path.canonicalPathCrossIsMinusOne

validationPointedTen : Integration.pointedTenCount ≡ 10
validationPointedTen = Integration.pointedTenCountIsTen

validationPointedEleven : Integration.pointedElevenCount ≡ 11
validationPointedEleven = Integration.pointedElevenCountIsEleven

validationSpiralProjection :
  Spiral.projectAddress Spiral.address1
  ≡ Spiral.projectAddress Spiral.address10
validationSpiralProjection = Spiral.oneTenProjectedSeam

validationSpiralDepth :
  Spiral.addressDepth Spiral.address11
  ≡ Spiral.addressDepth Spiral.address10 + 1
validationSpiralDepth = Spiral.tenElevenAdvanceDepth
