module DASHI.Base369MonsterTwoComponentCompletionValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Moonshine.Base369MonsterTwoComponentCompletionBidiExact as Two

------------------------------------------------------------------------
-- Primary/secondary two-component decomposition.
------------------------------------------------------------------------

fullPrimaryPinned :
  Two.primary369Component Two.fullWeightTwoTwoComponent ≡ 196830
fullPrimaryPinned = Two.fullPrimaryIs196830

reducedPrimaryPinned :
  Two.primary369Component Two.reducedMonsterTwoComponent ≡ 196830
reducedPrimaryPinned = Two.reducedPrimaryIs196830

primaryIsSameAcrossFullAndReduced :
  Two.primary369Component Two.fullWeightTwoTwoComponent
  ≡ Two.primary369Component Two.reducedMonsterTwoComponent
primaryIsSameAcrossFullAndReduced = Two.samePrimaryComponent

fullSecondaryPinned :
  Two.secondary369Component Two.fullWeightTwoTwoComponent ≡ 54
fullSecondaryPinned = Two.fullSecondaryIs54

reducedSecondaryPinned :
  Two.secondary369Component Two.reducedMonsterTwoComponent ≡ 53
reducedSecondaryPinned = Two.reducedSecondaryIs53

fullTwoComponentTotalPinned :
  Two.totalDimension Two.fullWeightTwoTwoComponent ≡ 196884
fullTwoComponentTotalPinned = Two.fullTotalIs196884

reducedTwoComponentTotalPinned :
  Two.totalDimension Two.reducedMonsterTwoComponent ≡ 196883
reducedTwoComponentTotalPinned = Two.reducedTotalIs196883

------------------------------------------------------------------------
-- Multiple repo-native 369 constructions of 54 / 53.
------------------------------------------------------------------------

secondarySixByNinePinned : 6 * 9 ≡ 54
secondarySixByNinePinned = refl

secondaryTwentySevenPlusTwentySevenPinned : 27 + 27 ≡ 54
secondaryTwentySevenPlusTwentySevenPinned = refl

secondaryFortyFivePlusNinePinned : 45 + 9 ≡ 54
secondaryFortyFivePlusNinePinned = Two.secondaryFullAsFortyFivePlusNine

secondaryFortyFivePlusEightPinned : 45 + 8 ≡ 53
secondaryFortyFivePlusEightPinned = Two.secondaryReducedAsFortyFivePlusEight

secondaryOnePlusReducedPinned : 1 + 53 ≡ 54
secondaryOnePlusReducedPinned = Two.secondaryOnePlusReduced

------------------------------------------------------------------------
-- Nested completion shapes.
------------------------------------------------------------------------

coarseNinePlusOnePinned :
  Two.completedPart Two.coarseNineToTenShape ≡ 10
coarseNinePlusOnePinned = refl

secondaryFiftyThreePlusOnePinned :
  Two.completedPart Two.secondaryFiftyThreeToFiftyFourShape ≡ 54
secondaryFiftyThreePlusOnePinned = refl

weightTwoMonsterPlusOnePinned :
  Two.completedPart Two.weightTwoMonsterToMoonshineShape ≡ 196884
weightTwoMonsterPlusOnePinned = refl

nestedFullPinned : Two.nestedFull369Dimension ≡ 196884
nestedFullPinned = Two.nestedFull369DimensionIs196884

nestedReducedPinned : Two.nestedReduced369Dimension ≡ 196883
nestedReducedPinned = Two.nestedReduced369DimensionIs196883

------------------------------------------------------------------------
-- Unit-role type separation.
------------------------------------------------------------------------

jUnitContributesFineFibre :
  Two.unitContribution Two.coarseJCompletionUnit ≡ 19683
jUnitContributesFineFibre = Two.coarseJUnitContributesFullFineFibre

secondaryUnitContributesOne :
  Two.unitContribution Two.secondaryInvariantUnit ≡ 1
secondaryUnitContributesOne = Two.secondaryUnitContributesOneDimension

conformalUnitContributesOne :
  Two.unitContribution Two.weightTwoConformalUnit ≡ 1
conformalUnitContributesOne = Two.conformalUnitContributesOneDimension

jUnitNotSecondaryUnit :
  Two.coarseJCompletionUnit ≡ Two.secondaryInvariantUnit → ⊥
jUnitNotSecondaryUnit = Two.coarseJIsNotSecondaryInvariant

secondaryUnitNotConformalUnit :
  Two.secondaryInvariantUnit ≡ Two.weightTwoConformalUnit → ⊥
secondaryUnitNotConformalUnit = Two.secondaryInvariantIsNotConformal

samePatternDoesNotIdentifyRepresentations :
  Two.MonsterTwoComponentCompletionBoundary.sameOnePlusShapeImpliesSameRepresentation
    Two.canonicalMonsterTwoComponentCompletionBoundary ≡ false
samePatternDoesNotIdentifyRepresentations = refl

fiftyThreeNotPromotedToMonsterIrrep :
  Two.MonsterTwoComponentCompletionBoundary.reducedFiftyThreeProvedMonsterIrreducibleHere
    Two.canonicalMonsterTwoComponentCompletionBoundary ≡ false
fiftyThreeNotPromotedToMonsterIrrep = refl
