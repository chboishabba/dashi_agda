module DASHI.Base369MonsterTwoComponentCompletionValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Moonshine.Base369MonsterTwoComponentCompletionBidiExact as Two
import DASHI.Moonshine.Base369ZetaHeisenbergFiftyFourCarrierExact as Z54

------------------------------------------------------------------------
-- Primary/secondary two-component COUNT decomposition.
--
-- The 53/54 numbers are treated first as structured finite carrier counts.
-- Mode/representation dimension language is only inherited where a separate
-- owner actually supplies that interpretation.
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

fullSecondaryCountPinned :
  Two.secondary369Component Two.fullWeightTwoTwoComponent ≡ 54
fullSecondaryCountPinned = Two.fullSecondaryIs54

reducedSecondaryCountPinned :
  Two.secondary369Component Two.reducedMonsterTwoComponent ≡ 53
reducedSecondaryCountPinned = Two.reducedSecondaryIs53

------------------------------------------------------------------------
-- The primitive 54 geometry is the zeta-pair / ternary factorisation.
------------------------------------------------------------------------

zetaPairTimesTwentySevenPinned : Z54.zeta54SiteCount ≡ 54
zetaPairTimesTwentySevenPinned = Z54.zeta54SiteCountIsFiftyFour

zetaTritFactorPinned : Z54.zetaTritCount ≡ 6
zetaTritFactorPinned = Z54.zetaTritCountIsSix

nonaryFactorPinned : Z54.nonaryPointCount ≡ 9
nonaryFactorPinned = Z54.nonaryPointCountIsNine

secondarySixByNinePinned : 6 * 9 ≡ 54
secondarySixByNinePinned = Z54.fiftyFourIsSixTimesNine

secondaryTwentySevenPlusTwentySevenPinned : 27 + 27 ≡ 54
secondaryTwentySevenPlusTwentySevenPinned = refl

------------------------------------------------------------------------
-- 53 is then available as the one-constant-mode reduction of that 54-count,
-- while the concrete line/mode interpretation remains separately typed.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Unit-role type separation.
------------------------------------------------------------------------

jUnitContributesFineFibre :
  Two.unitContribution Two.coarseJCompletionUnit ≡ 19683
jUnitContributesFineFibre = Two.coarseJUnitContributesFullFineFibre

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

fiftyFourIsNotHeisenbergRepresentationDimension :
  Z54.ZetaHeisenbergFiftyFourBoundary.fiftyFourIsHeisenbergRepresentationDimension
    Z54.canonicalZetaHeisenbergFiftyFourBoundary ≡ false
fiftyFourIsNotHeisenbergRepresentationDimension = refl
