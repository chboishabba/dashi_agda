module DASHI.Moonshine.Base369MonsterTwoComponentCompletionBidiExact where

------------------------------------------------------------------------
-- MONSTER FIRST-COEFFICIENT / CONSTITUENT AS TWO STRUCTURED 369 COMPONENTS
--
-- The repository already has two independently structured pieces:
--
--   primary   = (9 ordinary coarse channels + completion j) * 3^9
--             = 10 * 19683 = 196830
--
--   secondary-full    = 6 * 9 = 54
--   secondary-reduced = 54 - 1 = 53.
--
-- This owner makes that TWO-COMPONENT decomposition first-class instead of
-- treating 53/54 as an unstructured tail.  It also records the repeated
-- one-plus pattern
--
--   10     = 9 + 1
--   54     = 53 + 1
--   196884 = 196883 + 1
--
-- while preserving the existing type boundary: the included j completion,
-- the removed invariant line of the 54-carrier, and the weight-two conformal
-- line are different roles in different carriers.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Empty using (⊥)

import DASHI.Moonshine.Base369DecimalCompletionMonsterBulkBidiExact as Bulk
import DASHI.Moonshine.MonsterReducedNonaryBoundaryExact as Nonary
import DASHI.Biology.ReducedFiftyThreeFibreExact as Reduced
import DASHI.Biology.TernaryHypercubeHyperfabricExact as Hyper
import DASHI.Biology.JCompletionTrivialLineSeparationExact as Units
import DASHI.Biology.MoonshineConformalReductionVsFiftyFourReductionExact as Reduction
import DASHI.Biology.MoonshineVacuumConformalLineBoundaryExact as Grade

------------------------------------------------------------------------
-- 1. The two structured components.
------------------------------------------------------------------------

record TwoComponentDimension : Set where
  constructor twoComponentDimension
  field
    primary369Component : Nat
    secondary369Component : Nat
    totalDimension : Nat
    totalIsPrimaryPlusSecondary :
      totalDimension ≡ primary369Component + secondary369Component
open TwoComponentDimension public

fullWeightTwoTwoComponent : TwoComponentDimension
fullWeightTwoTwoComponent =
  twoComponentDimension Bulk.base369TenChannelBulk Reduced.fullSixByNineDimension 196884 refl

reducedMonsterTwoComponent : TwoComponentDimension
reducedMonsterTwoComponent =
  twoComponentDimension Bulk.base369TenChannelBulk Reduced.reducedDimension 196883 refl

fullPrimaryIs196830 :
  primary369Component fullWeightTwoTwoComponent ≡ 196830
fullPrimaryIs196830 = Bulk.base369TenChannelBulkIs196830

reducedPrimaryIs196830 :
  primary369Component reducedMonsterTwoComponent ≡ 196830
reducedPrimaryIs196830 = Bulk.base369TenChannelBulkIs196830

samePrimaryComponent :
  primary369Component fullWeightTwoTwoComponent
  ≡ primary369Component reducedMonsterTwoComponent
samePrimaryComponent = refl

fullSecondaryIs54 :
  secondary369Component fullWeightTwoTwoComponent ≡ 54
fullSecondaryIs54 = Reduced.fullSixByNineDimensionIsFiftyFour

reducedSecondaryIs53 :
  secondary369Component reducedMonsterTwoComponent ≡ 53
reducedSecondaryIs53 = Reduced.reducedDimensionIsFiftyThree

fullTotalIs196884 : totalDimension fullWeightTwoTwoComponent ≡ 196884
fullTotalIs196884 = refl

reducedTotalIs196883 : totalDimension reducedMonsterTwoComponent ≡ 196883
reducedTotalIs196883 = refl

------------------------------------------------------------------------
-- 2. The secondary 54 carrier has multiple existing 369 constructions.
------------------------------------------------------------------------

secondaryAsSixByNine : Hyper.siteCount Hyper.sheetSixByNine ≡ 54
secondaryAsSixByNine = Hyper.siteCountSixByNineIsFiftyFour

secondaryAsTwoTwentySevenMasses :
  Reduced.positiveMass Reduced.canonicalBalancedSixByNineMass
  + Reduced.negativeMass Reduced.canonicalBalancedSixByNineMass
  ≡ 54
secondaryAsTwoTwentySevenMasses = Reduced.canonicalBalancedTotalIsFiftyFour

secondaryAsFiveNonaryPlusOneNonary : 5 * 9 + 9 ≡ 54
secondaryAsFiveNonaryPlusOneNonary = Nonary.fiftyFourIsFiveTimesNinePlusNine

secondaryAsInvariantPlusFluctuation :
  Reduced.trivialInvariantDimension + Reduced.reducedDimension
  ≡ Reduced.fullSixByNineDimension
secondaryAsInvariantPlusFluctuation = Reduced.fullSplitsAsInvariantPlusReduced

secondaryZeroPlusNonzeroModeCount :
  Reduced.zeroModes Reduced.canonicalSixByNineModeCount
  + Reduced.nonzeroModes Reduced.canonicalSixByNineModeCount
  ≡ Reduced.totalModes Reduced.canonicalSixByNineModeCount
secondaryZeroPlusNonzeroModeCount =
  Reduced.modeCountCertificate Reduced.canonicalSixByNineModeCount

------------------------------------------------------------------------
-- 3. The reduced 53 carrier is the same secondary branch with one invariant
--    mode removed, and also the localised 45 + 8 nonary construction.
------------------------------------------------------------------------

secondaryReducedAsFortyFivePlusEight : 45 + 8 ≡ 53
secondaryReducedAsFortyFivePlusEight = Nonary.fiftyThreeIsFortyFivePlusEight

secondaryFullAsFortyFivePlusNine : 45 + 9 ≡ 54
secondaryFullAsFortyFivePlusNine = Nonary.fiftyFourIsFortyFivePlusNine

secondaryOnePlusReduced : 1 + 53 ≡ 54
secondaryOnePlusReduced = refl

secondaryReductionAgreesWithCanonicalFibre :
  Nonary.reducedSixByNine ≡ Reduced.reducedDimension
secondaryReductionAgreesWithCanonicalFibre =
  Nonary.localisedReductionAgreesWithExistingReducedDimension

------------------------------------------------------------------------
-- 4. Repeated one-plus completion/reduction SHAPE.
--
-- The shape is shared.  The concrete unit is not.
------------------------------------------------------------------------

record OnePlusShape : Set where
  constructor onePlusShape
  field
    reducedPart : Nat
    completedPart : Nat
    completionLaw : completedPart ≡ 1 + reducedPart
open OnePlusShape public

coarseNineToTenShape : OnePlusShape
coarseNineToTenShape = onePlusShape 9 10 refl

secondaryFiftyThreeToFiftyFourShape : OnePlusShape
secondaryFiftyThreeToFiftyFourShape = onePlusShape 53 54 refl

weightTwoMonsterToMoonshineShape : OnePlusShape
weightTwoMonsterToMoonshineShape = onePlusShape 196883 196884 refl

existingSecondaryReductionShapeAgrees :
  Reduction.totalDimension Reduction.fiftyFourToFiftyThreeReduction ≡ 54
existingSecondaryReductionShapeAgrees = refl

existingWeightTwoReductionShapeAgrees :
  Reduction.totalDimension Reduction.moonshineWeightTwoReduction ≡ 196884
existingWeightTwoReductionShapeAgrees = refl

------------------------------------------------------------------------
-- 5. The three unit roles are explicit and constructor-distinct.
------------------------------------------------------------------------

data CompletionUnitRole : Set where
  coarseJCompletionUnit : CompletionUnitRole
  secondaryInvariantUnit : CompletionUnitRole
  weightTwoConformalUnit : CompletionUnitRole

unitMultiplicity : CompletionUnitRole → Nat
unitMultiplicity coarseJCompletionUnit = 1
unitMultiplicity secondaryInvariantUnit = 1
unitMultiplicity weightTwoConformalUnit = 1

unitContribution : CompletionUnitRole → Nat
unitContribution coarseJCompletionUnit = Units.roleContribution Units.includedCompletionChannel
unitContribution secondaryInvariantUnit = Units.roleContribution Units.removedTrivialRepresentation
unitContribution weightTwoConformalUnit = Grade.weightTwoConformalMultiplicity

coarseJUnitContributesFullFineFibre :
  unitContribution coarseJCompletionUnit ≡ 19683
coarseJUnitContributesFullFineFibre = refl

secondaryUnitContributesOneDimension :
  unitContribution secondaryInvariantUnit ≡ 1
secondaryUnitContributesOneDimension = refl

conformalUnitContributesOneDimension :
  unitContribution weightTwoConformalUnit ≡ 1
conformalUnitContributesOneDimension = refl

coarseJIsNotSecondaryInvariant :
  coarseJCompletionUnit ≡ secondaryInvariantUnit → ⊥
coarseJIsNotSecondaryInvariant ()

secondaryInvariantIsNotConformal :
  secondaryInvariantUnit ≡ weightTwoConformalUnit → ⊥
secondaryInvariantIsNotConformal ()

coarseJIsNotConformal :
  coarseJCompletionUnit ≡ weightTwoConformalUnit → ⊥
coarseJIsNotConformal ()

existingJUnitRolesAreDistinct :
  Units.includedCompletionChannel ≡ Units.removedTrivialRepresentation → ⊥
existingJUnitRolesAreDistinct = Units.unitRolesAreDistinct

existingConformalAndFiftyFourLinesAreDistinct :
  Reduction.moonshineConformalRemovedLine
  ≡ Reduction.fiftyFourInvariantRemovedLine → ⊥
existingConformalAndFiftyFourLinesAreDistinct = Reduction.removedLinesAreDistinct

------------------------------------------------------------------------
-- 6. Nested exact decomposition.
--
-- Full:
--   ((9 + 1) * 3^9) + (53 + 1) = 196884
-- Reduced:
--   ((9 + 1) * 3^9) + 53       = 196883.
------------------------------------------------------------------------

nestedFull369Dimension : Nat
nestedFull369Dimension = (9 + 1) * Hyper.ternaryLatticeCount 9 + (53 + 1)

nestedReduced369Dimension : Nat
nestedReduced369Dimension = (9 + 1) * Hyper.ternaryLatticeCount 9 + 53

nestedFull369DimensionIs196884 : nestedFull369Dimension ≡ 196884
nestedFull369DimensionIs196884 = refl

nestedReduced369DimensionIs196883 : nestedReduced369Dimension ≡ 196883
nestedReduced369DimensionIs196883 = refl

fullDiffersFromReducedOnlyBySecondaryUnit :
  totalDimension fullWeightTwoTwoComponent
  ≡ 1 + totalDimension reducedMonsterTwoComponent
fullDiffersFromReducedOnlyBySecondaryUnit = refl

------------------------------------------------------------------------
-- 7. BIDI boundary.
------------------------------------------------------------------------

record MonsterTwoComponentCompletionBoundary : Set where
  constructor monsterTwoComponentCompletionBoundary
  field
    primaryAndSecondaryComponentsExplicit : Bool
    primaryComponentIsTenTimesThreePowerNine : Bool
    secondaryFullHasCanonicalSixByNineOrigin : Bool
    secondaryFullHasBalancedTwentySevenPlusTwentySevenOrigin : Bool
    secondaryReducedIsFiftyThreeFluctuationModes : Bool
    repeatedOnePlusShapeIsExact : Bool
    jUnitEqualsSecondaryInvariantUnit : Bool
    secondaryInvariantEqualsConformalLine : Bool
    sameOnePlusShapeImpliesSameRepresentation : Bool
    reducedFiftyThreeProvedMonsterIrreducibleHere : Bool
    fiftyFourFiftySixSixtyFourGluingSemanticsProvedHere : Bool

canonicalMonsterTwoComponentCompletionBoundary : MonsterTwoComponentCompletionBoundary
canonicalMonsterTwoComponentCompletionBoundary =
  monsterTwoComponentCompletionBoundary
    true true true true true true
    false false false false false
