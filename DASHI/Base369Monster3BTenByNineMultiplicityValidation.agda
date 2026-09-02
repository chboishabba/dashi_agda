module DASHI.Base369Monster3BTenByNineMultiplicityValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Moonshine.Base369Monster3BMultiplicityTenByNineBidiExact as Ninety
import DASHI.Moonshine.Base369Pointed729NestedNinetyBidiExact as Nested
import DASHI.Moonshine.Base369MonsterThreeLocalTenByNineRefactorBidiExact as ThreeLocal
import DASHI.Moonshine.Base369Monster3BRepresentationBidiSearchRound11Exact as Round11

ninetyIsTypedTenByNine : Ninety.tenByNineDimension ≡ 90
ninetyIsTypedTenByNine = Ninety.tenByNineDimensionIsNinety

nestedPointed729IsExact : Nested.nestedPointedDimension ≡ 729
nestedPointed729IsExact = Nested.nestedPointedDimensionIs729

nestedZeta65610IsExact : Nested.nestedZetaDimension ≡ 65610
nestedZeta65610IsExact = Nested.nestedZetaDimensionIs65610

nestedThreePhase196830IsExact :
  Nested.nestedThreePhaseBulkDimension ≡ 196830
nestedThreePhase196830IsExact = Nested.nestedThreePhaseBulkDimensionIs196830

threeLocalRefactor65610IsExact :
  Ninety.tenByNineDimension *
    DASHI.Moonshine.MonsterThreeLocalE8LeechBridgeExact.threePowerSix
  ≡ 65610
threeLocalRefactor65610IsExact = ThreeLocal.tenByNineTimesThreePowerSixIs65610

sameActualActionRequired :
  Ninety.MultiplicityTenByNineBoundary.sameActualMultiplicityActionRequired
    Ninety.canonicalMultiplicityTenByNineBoundary ≡ true
sameActualActionRequired = refl

dimensionAloneDoesNotPromote :
  Ninety.MultiplicityTenByNineBoundary.dimensionNinetyAlonePromotesRecognition
    Ninety.canonicalMultiplicityTenByNineBoundary ≡ false
dimensionAloneDoesNotPromote = refl

nestedShapeDoesNotCreateMonsterAction :
  Nested.NestedNinetyBoundary.recursiveNinetyShapeAloneIdentifiesMonsterAction
    Nested.canonicalNestedNinetyBoundary ≡ false
nestedShapeDoesNotCreateMonsterAction = refl

threeLocalGroupsRemainDistinct :
  ThreeLocal.ThreeLocalTenByNineBoundary.threePowerEightGroupIdentifiedWithExtraspecialKernel
    ThreeLocal.canonicalThreeLocalTenByNineBoundary ≡ false
threeLocalGroupsRemainDistinct = refl

outerTenByNineRecognitionStillLive :
  Round11.Round11Status.fin90MultiplicityToTenByNineRecognition
    Round11.canonicalRound11Status ≡ false
outerTenByNineRecognitionStillLive = refl
