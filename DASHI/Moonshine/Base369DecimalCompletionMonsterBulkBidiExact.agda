module DASHI.Moonshine.Base369DecimalCompletionMonsterBulkBidiExact where

------------------------------------------------------------------------
-- DECIMAL / NONARY COMPLETION <-> BASE369 / MONSTER BULK BIDI LEDGER
--
-- This owner records exact arithmetic already distributed across the repo:
--
--   ordinary coarse channels + completion j = 9 + 1 = 10
--   one Base369 fine hyperfabric                = 3^9 = 19683
--   ten coarse channels x one fine hyperfabric = 196830
--   Monster dimension                           = 196830 + 53
--   moonshine weight-two dimension              = 196830 + 54
--
-- It also separates the decimal occupancy ladder
--   9/10, 99/100, 999/1000, ...
-- from the reciprocal completion scale 10/9.  Exact arithmetic agreement does
-- not by itself prove a geometric or Monster-semantic interpretation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)

import DASHI.Foundations.DecimalNonaryRefinementBridgeExact as Decimal
import DASHI.Biology.BalancedTernaryHarmonicCarrierExact as Harmonic
import DASHI.Biology.NonaryCompletionPhaseQuotientExact as Completion
import DASHI.Biology.JFineCoarseRelativeScaleExact as JScale
import DASHI.Core.CoarseFineBranchAccessibilityExact as Branch
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Moonshine.MonsterReducedNonaryBoundaryExact as Monster

------------------------------------------------------------------------
-- 1. Exact 9 + j = 10 coarse-channel structure.
------------------------------------------------------------------------

ordinaryCoarseChannelCount : Nat
ordinaryCoarseChannelCount = Harmonic.ordinaryCoarseDimension

completionChannelCount : Nat
completionChannelCount = Harmonic.completionCoarseDimension

coarseWithCompletionCount : Nat
coarseWithCompletionCount = ordinaryCoarseChannelCount + completionChannelCount

ordinaryCoarseCountIsNine : ordinaryCoarseChannelCount ≡ 9
ordinaryCoarseCountIsNine = refl

completionCountIsOne : completionChannelCount ≡ 1
completionCountIsOne = refl

coarseWithCompletionCountIsTen : coarseWithCompletionCount ≡ 10
coarseWithCompletionCountIsTen = refl

decimalCompletionCarrierAlsoHasTen :
  Completion.listCount Completion.canonicalDecimalCompletionStates ≡ 10
decimalCompletionCarrierAlsoHasTen = Completion.decimalCompletionStateCountIsTen

------------------------------------------------------------------------
-- 2. 9/10 -> 99/100 -> 999/1000 as exact normalized occupancy addresses.
------------------------------------------------------------------------

record DecimalOccupancy : Set where
  constructor decimalOccupancy
  field numerator denominator : Nat
open DecimalOccupancy public

nineTenths : DecimalOccupancy
nineTenths = decimalOccupancy 9 10

ninetyNineHundredths : DecimalOccupancy
ninetyNineHundredths = decimalOccupancy 99 100

nineNineNineThousandths : DecimalOccupancy
nineNineNineThousandths = decimalOccupancy 999 1000

nineTenthsHasUnitComplement : denominator nineTenths ≡ numerator nineTenths + 1
nineTenthsHasUnitComplement = refl

ninetyNineHundredthsHasUnitComplement :
  denominator ninetyNineHundredths ≡ numerator ninetyNineHundredths + 1
ninetyNineHundredthsHasUnitComplement = refl

nineNineNineThousandthsHasUnitComplement :
  denominator nineNineNineThousandths ≡ numerator nineNineNineThousandths + 1
nineNineNineThousandthsHasUnitComplement = refl

-- Existing decimal owner stores repeated 9 as 9.9, 9.99, 9.999 ... .
-- Normalising by one additional factor of ten gives the occupancy sequence.

existingNineFirstRefinementNumerator :
  Decimal.scaledNumerator (Decimal.canonicalDecimalRefinement Decimal.d9 1) ≡ 99
existingNineFirstRefinementNumerator = Decimal.nineFirstRefinementIs99Tenths

existingNineThirdRefinementNumerator :
  Decimal.scaledNumerator (Decimal.canonicalDecimalRefinement Decimal.d9 3) ≡ 9999
existingNineThirdRefinementNumerator = Decimal.nineThirdRefinementIs9999Thousandths

------------------------------------------------------------------------
-- 3. Reciprocal 10/9 completion scale is already exact in the decimal owner.
------------------------------------------------------------------------

tenOverNineTargetAtNineIsExactCarry :
  Decimal.nextBandScaledNumerator Decimal.d9
  ≡ Decimal.refinementTargetNumerator Decimal.d9
tenOverNineTargetAtNineIsExactCarry = Decimal.nineTargetCarriesExactly

tenTimesNineEqualsNineTimesTen : 10 * 9 ≡ 9 * 10
tenTimesNineEqualsNineTimesTen = refl

------------------------------------------------------------------------
-- 4. The three-axis 9/10 numerator reaches the actual Base369 fine count.
------------------------------------------------------------------------

ninetyPercentThreeAxisNumeratorIsHyperfabric :
  Branch.jointExpectedNumerator 3 3 (Branch.availability 9 10)
  ≡ Geometry.hyperfabricStateCount
ninetyPercentThreeAxisNumeratorIsHyperfabric =
  Decimal.ninetyPercentThreeAxisNumeratorMatchesJFine

jFineEqualsHyperfabricCount :
  JScale.jFineFrequency ≡ Geometry.hyperfabricStateCount
jFineEqualsHyperfabricCount = refl

------------------------------------------------------------------------
-- 5. Ten coarse channels times one Base369 hyperfabric = Monster bulk.
------------------------------------------------------------------------

base369TenChannelBulk : Nat
base369TenChannelBulk = coarseWithCompletionCount * Geometry.hyperfabricStateCount

base369TenChannelBulkIs196830 : base369TenChannelBulk ≡ 196830
base369TenChannelBulkIs196830 = refl

base369BulkAgreesWithHarmonicElementaryDimension :
  base369TenChannelBulk ≡ Harmonic.elementaryHarmonicDimension
base369BulkAgreesWithHarmonicElementaryDimension = refl

base369BulkAgreesWithMonsterBulk :
  base369TenChannelBulk ≡ Monster.monsterBulk
base369BulkAgreesWithMonsterBulk = refl

------------------------------------------------------------------------
-- 6. Existing +53 / +54 completions now share the same explicit bulk owner.
------------------------------------------------------------------------

monsterDimensionFromBase369Bulk : Nat
monsterDimensionFromBase369Bulk = base369TenChannelBulk + Monster.reducedSixByNine

moonshineWeightTwoFromBase369Bulk : Nat
moonshineWeightTwoFromBase369Bulk = base369TenChannelBulk + Monster.fullSixByNine

monsterDimensionFromBase369BulkIs196883 :
  monsterDimensionFromBase369Bulk ≡ 196883
monsterDimensionFromBase369BulkIs196883 = refl

moonshineWeightTwoFromBase369BulkIs196884 :
  moonshineWeightTwoFromBase369Bulk ≡ 196884
moonshineWeightTwoFromBase369BulkIs196884 = refl

reducedResidualIsFiveNonaryPlusEight : Monster.reducedSixByNine ≡ 5 * 9 + 8
reducedResidualIsFiveNonaryPlusEight = refl

fullResidualIsSixNonarySectors : Monster.fullSixByNine ≡ 6 * 9
fullResidualIsSixNonarySectors = refl

------------------------------------------------------------------------
-- 7. BIDI boundary.
------------------------------------------------------------------------

record DecimalCompletionMonsterBulkBoundary : Set where
  constructor decimalCompletionMonsterBulkBoundary
  field
    nineOrdinaryPlusCompletionIsTen : Bool
    tenTimesBase369FineIsMonsterBulk : Bool
    nineTenthsThreeAxisNumeratorMatchesFineCount : Bool
    tenOverNineCompletionIdentityAvailable : Bool
    plusFiftyThreeArithmeticRecovered : Bool
    plusFiftyFourArithmeticRecovered : Bool
    decimalLadderCausesMonsterDimension : Bool
    completionJIsOrdinaryTorusResidue : Bool
    fiftyThreeAlreadyHasGeometricGluingInterpretation : Bool

canonicalDecimalCompletionMonsterBulkBoundary : DecimalCompletionMonsterBulkBoundary
canonicalDecimalCompletionMonsterBulkBoundary =
  decimalCompletionMonsterBulkBoundary
    true true true true true true false false false
