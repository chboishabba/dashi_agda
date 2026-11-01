module DASHI.Biology.ThreeSixNineMoonshineScaleExact where

open import DASHI.Core.Prelude

import DASHI.Biology.PointedTernaryBulkExact as Pointed
import DASHI.Biology.DecimalTenTernaryPresentationExact as Decimal
import DASHI.Biology.ReducedFiftyThreeFibreExact as Reduced
import DASHI.Biology.TernaryHypercubeHyperfabricExact as Hyper
import DASHI.Biology.TernaryMonsterSymmetryCandidateExact as Symmetry

------------------------------------------------------------------------
-- Exact shared arithmetic of the 3 / 6 / 9 / 10 / 27 / 54 spine.
-- The equalities coexist, but their interpretations remain separately typed.
------------------------------------------------------------------------

triadicBase : Nat
triadicBase = 3

binaryOrientationCount : Nat
binaryOrientationCount = 2

sixScale : Nat
sixScale = triadicBase * binaryOrientationCount

nineScale : Nat
nineScale = triadicBase * triadicBase

tenScaleFromPointing : Nat
tenScaleFromPointing = 1 + nineScale

tenScaleFromIrrepOrientation : Nat
tenScaleFromIrrepOrientation = 5 * binaryOrientationCount

twentySevenScale : Nat
twentySevenScale = triadicBase * nineScale

fiftyFourScale : Nat
fiftyFourScale = sixScale * nineScale

sixScaleIsSix : sixScale ≡ 6
sixScaleIsSix = refl

nineScaleIsNine : nineScale ≡ 9
nineScaleIsNine = refl

tenScaleFromPointingIsTen : tenScaleFromPointing ≡ 10
tenScaleFromPointingIsTen = refl

tenScaleFromIrrepOrientationIsTen :
  tenScaleFromIrrepOrientation ≡ 10
tenScaleFromIrrepOrientationIsTen = refl

twentySevenScaleIsTwentySeven : twentySevenScale ≡ 27
twentySevenScaleIsTwentySeven = refl

fiftyFourScaleIsFiftyFour : fiftyFourScale ≡ 54
fiftyFourScaleIsFiftyFour = refl

fiftyFourIsTwoTimesThreeCubed :
  fiftyFourScale ≡
  binaryOrientationCount * Hyper.ternaryLatticeCount 3
fiftyFourIsTwoTimesThreeCubed = refl

fiftyFourMatchesSixByNineCarrier :
  fiftyFourScale ≡ Reduced.fullSixByNineDimension
fiftyFourMatchesSixByNineCarrier = refl

tenPointingMatchesMarkerCount :
  tenScaleFromPointing ≡ Pointed.markerCount
tenPointingMatchesMarkerCount = refl

tenIrrepOrientationMatchesSectorCount :
  tenScaleFromIrrepOrientation
  ≡ Symmetry.listCount Symmetry.canonicalTenSectors
tenIrrepOrientationMatchesSectorCount = refl

fiftyFourSplitsInvariantAndReduced :
  fiftyFourScale
  ≡ Reduced.trivialInvariantDimension + Reduced.reducedDimension
fiftyFourSplitsInvariantAndReduced = refl

------------------------------------------------------------------------
-- Complete coefficient arithmetic expressed through the scale ledger.
------------------------------------------------------------------------

ternaryNineConfigurationCount : Nat
ternaryNineConfigurationCount = Hyper.ternaryLatticeCount nineScale

ternaryNineConfigurationCountIs19683 :
  ternaryNineConfigurationCount ≡ 19683
ternaryNineConfigurationCountIs19683 = refl

regularBulkDimension : Nat
regularBulkDimension = tenScaleFromPointing * ternaryNineConfigurationCount

regularBulkDimensionIs196830 : regularBulkDimension ≡ 196830
regularBulkDimensionIs196830 = refl

fullCoefficientDimension : Nat
fullCoefficientDimension = regularBulkDimension + fiftyFourScale

reducedCoefficientDimension : Nat
reducedCoefficientDimension =
  regularBulkDimension + Reduced.reducedDimension

fullCoefficientDimensionIs196884 :
  fullCoefficientDimension ≡ 196884
fullCoefficientDimensionIs196884 = refl

reducedCoefficientDimensionIs196883 :
  reducedCoefficientDimension ≡ 196883
reducedCoefficientDimensionIs196883 = refl

------------------------------------------------------------------------
-- Authority separation.  The same numeral may receive several presentations;
-- only explicit bridges may transfer structure between them.
------------------------------------------------------------------------

data ScalePresentation : Set where
  triadicArithmeticPresentation : ScalePresentation
  pointedSitePresentation : ScalePresentation
  irrepOrientationPresentation : ScalePresentation
  sixByNineModePresentation : ScalePresentation
  moonshineCoefficientPresentation : ScalePresentation

record PresentationBridge : Set where
  constructor presentationBridge
  field
    sourcePresentation : ScalePresentation
    targetPresentation : ScalePresentation
    preservesCardinality : Bool
    preservesDeclaredAction : Bool
    preservesInterpretation : Bool

pointedToDecimalCardinalityBridge : PresentationBridge
pointedToDecimalCardinalityBridge =
  presentationBridge
    pointedSitePresentation
    triadicArithmeticPresentation
    true
    false
    false

irrepToDecimalCardinalityBridge : PresentationBridge
irrepToDecimalCardinalityBridge =
  presentationBridge
    irrepOrientationPresentation
    triadicArithmeticPresentation
    true
    false
    false

sixByNineToReducedModeBridge : PresentationBridge
sixByNineToReducedModeBridge =
  presentationBridge
    sixByNineModePresentation
    moonshineCoefficientPresentation
    true
    false
    false

record ThreeSixNineMoonshineScaleBoundary : Set where
  constructor threeSixNineMoonshineScaleBoundary
  field
    arithmeticEqualityTransfersGroupAction : Bool
    arithmeticEqualityTransfersGroupActionIsFalse :
      arithmeticEqualityTransfersGroupAction ≡ false

    fiveIrrepTypesAreFiveRawConstituents : Bool
    fiveIrrepTypesAreFiveRawConstituentsIsFalse :
      fiveIrrepTypesAreFiveRawConstituents ≡ false

    sixByNineCountConstructsLaplacianAdjacency : Bool
    sixByNineCountConstructsLaplacianAdjacencyIsFalse :
      sixByNineCountConstructsLaplacianAdjacency ≡ false

    coefficientArithmeticConstructsMoonshineModule : Bool
    coefficientArithmeticConstructsMoonshineModuleIsFalse :
      coefficientArithmeticConstructsMoonshineModule ≡ false

open ThreeSixNineMoonshineScaleBoundary public

canonicalThreeSixNineMoonshineScaleBoundary :
  ThreeSixNineMoonshineScaleBoundary
canonicalThreeSixNineMoonshineScaleBoundary =
  threeSixNineMoonshineScaleBoundary
    false refl
    false refl
    false refl
    false refl
