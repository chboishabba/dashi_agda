module DASHI.Moonshine.SSPJGluingMathieuRound6Validation where

open import DASHI.Core.Prelude

import DASHI.Biology.EisensteinNineRingInterferenceExact as Eisenstein
import DASHI.Biology.HalfChartNineRingQuotientExact as Half
import DASHI.Biology.IndexedJExternalGluingExact as Gluing
import DASHI.Biology.IteratedPointedAttachmentSpiralExact as Spiral
import DASHI.Moonshine.MathieuDivisorLatticeExact as Divisor
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
  Eisenstein.realCoordinate Eisenstein.threePhaseSum ≡ Eisenstein.0ℚ
validationThreePhaseCancellationReal = Eisenstein.threePhaseCancellationReal

validationMonsterSplit : Monster.fibreInterferenceTotal ≡ 196884
validationMonsterSplit = Monster.fibreInterferenceTotalIs196884

validationMonsterCoarseTrace :
  Monster.coarseSectorDimension ≡ 54
validationMonsterCoarseTrace = Monster.coarseSectorDimensionIs54

validationM11Tower :
  Mathieu.levelOrder Mathieu.M11Level ≡ 8 * 9 * 10 * 11
validationM11Tower = Mathieu.m11OrderAsSuccessiveOrbits

validationM12Tower :
  Mathieu.levelOrder Mathieu.M12Level ≡ 8 * 9 * 10 * 11 * 12
validationM12Tower = Mathieu.m12OrderAsSuccessiveOrbits

validationM8NotD4 :
  Mathieu.atlasReportedM8Shape ≡ Mathieu.squareDihedralD4 → ⊥
validationM8NotD4 = Mathieu.atlasReportedM8IsNotD4

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
