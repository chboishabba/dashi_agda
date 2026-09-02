module DASHI.Base369Monster3BCornerTritSquareValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Foundations.Base369Ternary27CornerEightExact as Corners
import DASHI.Moonshine.Base369CompletedTenTritSquareMultiplicityBidiExact as Completed
import DASHI.Moonshine.Base369Pointed729CornerCubeBidiExact as Corner729
import DASHI.Moonshine.Base369Pointed729CornerTritSquareBidiExact as Full729
import DASHI.Moonshine.Base369MonsterThreeLocalEightToSixPlusTwoCarrierBidiExact as EightSplit
import DASHI.Moonshine.Base369Monster3BRepresentationBidiSearchRound12Exact as Round12

negativeCornerChartIsGeometric :
  Corners.fin8ToCorner Data.Fin.Base.zero
  ≡ Corners.corner3 Corners.negativeOuter Corners.negativeOuter Corners.negativeOuter
negativeCornerChartIsGeometric = refl

cornerIndexed729Is729 : Corner729.cornerFibreDimension ≡ 729
cornerIndexed729Is729 = Corner729.cornerFibreDimensionIs729

completedTenTritSquareNinety :
  Full729.completedTenTimesThreeSquared ≡ 90
completedTenTritSquareNinety = Full729.completedTenTimesThreeSquaredIsNinety

fullCornerCarrierIs729 : Full729.cornerCompletedDimension ≡ 729
fullCornerCarrierIs729 = Full729.cornerCompletedDimensionIsThreePowerSix

fullCornerCarrierTimesNinetyIs65610 :
  Full729.nestedRegularPhaseDimension ≡ 65610
fullCornerCarrierTimesNinetyIs65610 = Full729.nestedRegularPhaseDimensionIs65610

fullCornerThreePhaseBulkIs196830 :
  Full729.nestedThreePhaseBulkDimension ≡ 196830
fullCornerThreePhaseBulkIs196830 = Full729.nestedThreePhaseBulkDimensionIs196830

eightSplitsAsSixPlusTwoCarrier :
  (state : EightSplit.X8) →
  EightSplit.joinEight (EightSplit.splitEight state) ≡ state
eightSplitsAsSixPlusTwoCarrier = EightSplit.joinAfterSplit

cornerGeometryDoesNotConstructMonsterAction :
  Corners.CornerEightBoundary.geometricCornerChartConstructsMonsterAction
    Corners.canonicalCornerEightBoundary ≡ false
cornerGeometryDoesNotConstructMonsterAction = refl

outerMultiplicityRecognitionStillLive :
  Round12.Round12Status.outerFin90ToCompletedTenTritSquareRecognition
    Round12.canonicalRound12Status ≡ false
outerMultiplicityRecognitionStillLive = refl

threePowerEightActionRecognitionStillParallel :
  Round12.Round12Status.actualThreePowerEightActionRecognition
    Round12.canonicalRound12Status ≡ false
threePowerEightActionRecognitionStillParallel = refl
