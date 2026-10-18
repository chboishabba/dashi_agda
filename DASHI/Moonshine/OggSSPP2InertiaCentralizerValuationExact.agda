module DASHI.Moonshine.OggSSPP2InertiaCentralizerValuationExact where

------------------------------------------------------------------------
-- p=2 INERTIA CENTRALIZER 2-ADIC WEIGHT CANDIDATE
--
-- CLASSICAL GROUP DATA
--
-- The binary tetrahedral group 2T has order 24 and seven conjugacy classes of
-- sizes
--
--   1, 1, 6, 4, 4, 4, 4.
--
-- Hence the corresponding centralizer orders are
--
--   24, 24, 4, 6, 6, 6, 6.
--
-- Loop reversal / inversion fixes the identity, central -1 and order-4 class,
-- and pairs the two order-3 classes and the two order-6 classes.
--
-- Therefore one representative from each of the five UNORIENTED inertia
-- sectors has centralizer order
--
--   24, 24, 4, 6, 6.
--
-- Their 2-adic depths are
--
--   3, 3, 2, 1, 1,
--
-- summing to 10, exactly the Duncan--Swisher p=2 exceptional gap.
--
-- This is stronger than a count match: it is a canonical isotropy-weighted
-- p-adic sum on the classical supersingular inertia fibre.
--
-- It is STILL not a proof that this sum enters the Hauptmodul valuation.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Product using (_×_; _,_)

import DASHI.Moonshine.OggSSPP2BinaryTetrahedralInertiaFiveOrbitExact as Inertia
import DASHI.Moonshine.MonsterOrderExponentCorrectionExact as Exponent
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane
import DASHI.Moonshine.OggSSPSmallCharacteristicClassicalSourceAtlasExact as Classical
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Sourced conjugacy-class size surface.
------------------------------------------------------------------------

classSize :
  Inertia.BinaryTetrahedralConjugacyClass ->
  Nat
classSize Inertia.identityClass = 1
classSize Inertia.centralMinusOneClass = 1
classSize Inertia.orderFourClass = 6
classSize Inertia.orderThreePositiveClass = 4
classSize Inertia.orderThreeNegativeClass = 4
classSize Inertia.orderSixPositiveClass = 4
classSize Inertia.orderSixNegativeClass = 4

centralizerOrder :
  Inertia.BinaryTetrahedralConjugacyClass ->
  Nat
centralizerOrder Inertia.identityClass = 24
centralizerOrder Inertia.centralMinusOneClass = 24
centralizerOrder Inertia.orderFourClass = 4
centralizerOrder Inertia.orderThreePositiveClass = 6
centralizerOrder Inertia.orderThreeNegativeClass = 6
centralizerOrder Inertia.orderSixPositiveClass = 6
centralizerOrder Inertia.orderSixNegativeClass = 6

classSizeTimesCentralizerIsTwentyFour :
  (class : Inertia.BinaryTetrahedralConjugacyClass) ->
  classSize class * centralizerOrder class ≡ 24
classSizeTimesCentralizerIsTwentyFour Inertia.identityClass = refl
classSizeTimesCentralizerIsTwentyFour Inertia.centralMinusOneClass = refl
classSizeTimesCentralizerIsTwentyFour Inertia.orderFourClass = refl
classSizeTimesCentralizerIsTwentyFour Inertia.orderThreePositiveClass = refl
classSizeTimesCentralizerIsTwentyFour Inertia.orderThreeNegativeClass = refl
classSizeTimesCentralizerIsTwentyFour Inertia.orderSixPositiveClass = refl
classSizeTimesCentralizerIsTwentyFour Inertia.orderSixNegativeClass = refl

------------------------------------------------------------------------
-- 2. Exact 2-adic centralizer depths.
------------------------------------------------------------------------

centralizerTwoAdicDepth :
  Inertia.BinaryTetrahedralConjugacyClass ->
  Nat
centralizerTwoAdicDepth Inertia.identityClass = 3
centralizerTwoAdicDepth Inertia.centralMinusOneClass = 3
centralizerTwoAdicDepth Inertia.orderFourClass = 2
centralizerTwoAdicDepth Inertia.orderThreePositiveClass = 1
centralizerTwoAdicDepth Inertia.orderThreeNegativeClass = 1
centralizerTwoAdicDepth Inertia.orderSixPositiveClass = 1
centralizerTwoAdicDepth Inertia.orderSixNegativeClass = 1

identityCentralizerFactorization :
  centralizerOrder Inertia.identityClass ≡ 2 * 2 * 2 * 3
identityCentralizerFactorization = refl

minusOneCentralizerFactorization :
  centralizerOrder Inertia.centralMinusOneClass ≡ 2 * 2 * 2 * 3
minusOneCentralizerFactorization = refl

orderFourCentralizerFactorization :
  centralizerOrder Inertia.orderFourClass ≡ 2 * 2
orderFourCentralizerFactorization = refl

orderThreeCentralizerFactorization :
  centralizerOrder Inertia.orderThreePositiveClass ≡ 2 * 3
orderThreeCentralizerFactorization = refl

orderSixCentralizerFactorization :
  centralizerOrder Inertia.orderSixPositiveClass ≡ 2 * 3
orderSixCentralizerFactorization = refl

centralizerDepthInvariantUnderInversion :
  (class : Inertia.BinaryTetrahedralConjugacyClass) ->
  centralizerTwoAdicDepth (Inertia.inverseClass class)
  ≡ centralizerTwoAdicDepth class
centralizerDepthInvariantUnderInversion Inertia.identityClass = refl
centralizerDepthInvariantUnderInversion Inertia.centralMinusOneClass = refl
centralizerDepthInvariantUnderInversion Inertia.orderFourClass = refl
centralizerDepthInvariantUnderInversion Inertia.orderThreePositiveClass = refl
centralizerDepthInvariantUnderInversion Inertia.orderThreeNegativeClass = refl
centralizerDepthInvariantUnderInversion Inertia.orderSixPositiveClass = refl
centralizerDepthInvariantUnderInversion Inertia.orderSixNegativeClass = refl

------------------------------------------------------------------------
-- 3. Descend the depth to the five unoriented inertia sectors.
------------------------------------------------------------------------

unorientedCentralizerTwoAdicDepth :
  Inertia.BinaryTetrahedralInversionOrbit ->
  Nat
unorientedCentralizerTwoAdicDepth Inertia.identityInertiaOrbit = 3
unorientedCentralizerTwoAdicDepth Inertia.centralMinusOneInertiaOrbit = 3
unorientedCentralizerTwoAdicDepth Inertia.orderFourInertiaOrbit = 2
unorientedCentralizerTwoAdicDepth Inertia.orderThreePairInertiaOrbit = 1
unorientedCentralizerTwoAdicDepth Inertia.orderSixPairInertiaOrbit = 1

representativeClass :
  Inertia.BinaryTetrahedralInversionOrbit ->
  Inertia.BinaryTetrahedralConjugacyClass
representativeClass Inertia.identityInertiaOrbit = Inertia.identityClass
representativeClass Inertia.centralMinusOneInertiaOrbit =
  Inertia.centralMinusOneClass
representativeClass Inertia.orderFourInertiaOrbit = Inertia.orderFourClass
representativeClass Inertia.orderThreePairInertiaOrbit =
  Inertia.orderThreePositiveClass
representativeClass Inertia.orderSixPairInertiaOrbit =
  Inertia.orderSixPositiveClass

unorientedDepthIsRepresentativeCentralizerDepth :
  (orbit : Inertia.BinaryTetrahedralInversionOrbit) ->
  unorientedCentralizerTwoAdicDepth orbit
  ≡ centralizerTwoAdicDepth (representativeClass orbit)
unorientedDepthIsRepresentativeCentralizerDepth Inertia.identityInertiaOrbit = refl
unorientedDepthIsRepresentativeCentralizerDepth Inertia.centralMinusOneInertiaOrbit = refl
unorientedDepthIsRepresentativeCentralizerDepth Inertia.orderFourInertiaOrbit = refl
unorientedDepthIsRepresentativeCentralizerDepth Inertia.orderThreePairInertiaOrbit = refl
unorientedDepthIsRepresentativeCentralizerDepth Inertia.orderSixPairInertiaOrbit = refl

------------------------------------------------------------------------
-- 4. Weighted five-sector sum equals the p=2 Monster gap.
------------------------------------------------------------------------

p2UnorientedInertiaDepthSum : Nat
p2UnorientedInertiaDepthSum =
  unorientedCentralizerTwoAdicDepth Inertia.identityInertiaOrbit
  + unorientedCentralizerTwoAdicDepth Inertia.centralMinusOneInertiaOrbit
  + unorientedCentralizerTwoAdicDepth Inertia.orderFourInertiaOrbit
  + unorientedCentralizerTwoAdicDepth Inertia.orderThreePairInertiaOrbit
  + unorientedCentralizerTwoAdicDepth Inertia.orderSixPairInertiaOrbit

p2UnorientedInertiaDepthSumIsTen :
  p2UnorientedInertiaDepthSum ≡ 10
p2UnorientedInertiaDepthSumIsTen = refl

p2MonsterGapIsUnorientedInertiaCentralizerDepthSum :
  Exponent.monsterOrderExponent Lane.p2
  ≡
  Exponent.duncanSwisherExceptionalRHS Lane.p2
  + p2UnorientedInertiaDepthSum
p2MonsterGapIsUnorientedInertiaCentralizerDepthSum =
  Exponent.p2ExceptionalGap

------------------------------------------------------------------------
-- 5. Compare with the alternative ten-sector unit-rank model.
--
-- Both totals are ten, but they are different candidate MECHANISMS.
------------------------------------------------------------------------

data CentralizerDepthMechanismEqualsOrientationUnitRankMechanism : Set where

centralizerDepthMechanismNotIdentifiedWithOrientationUnitRank :
  CentralizerDepthMechanismEqualsOrientationUnitRankMechanism -> ⊥
centralizerDepthMechanismNotIdentifiedWithOrientationUnitRank ()

------------------------------------------------------------------------
-- 6. Attribution / theorem boundary.
------------------------------------------------------------------------

classicalBoundary :
  Classical.SmallCharacteristicClassicalSourcingBoundary
classicalBoundary =
  Classical.canonicalSmallCharacteristicClassicalSourcingBoundary

data CentralizerDepthSumIsHauptmodulValuationCorrection : Set where
data BinaryTetrahedralClassTableProvesMonsterExponent : Set where

centralizerDepthSumNotYetProvedAsHauptmodulCorrection :
  CentralizerDepthSumIsHauptmodulValuationCorrection -> ⊥
centralizerDepthSumNotYetProvedAsHauptmodulCorrection ()

classTableDoesNotProveMonsterExponent :
  BinaryTetrahedralClassTableProvesMonsterExponent -> ⊥
classTableDoesNotProveMonsterExponent ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryCrossModuleInference

record P2InertiaCentralizerValuationBoundary : Set where
  constructor p2-inertia-centralizer-valuation-boundary
  field
    sevenClassSizesSourced : Bool
    centralizerOrdersDerivedFromClassSizes : Bool
    twoAdicCentralizerDepthsExact : Bool
    depthsDescendThroughLoopReversal : Bool
    fiveUnorientedDepthsThreeThreeTwoOneOne : Bool
    depthSumIsTen : Bool
    depthSumPaysExactP2MonsterGap : Bool
    orientationDoubletNeededForThisWeightedSum : Bool
    hauptmodulCorrectionMechanismProved : Bool

canonicalP2InertiaCentralizerValuationBoundary :
  P2InertiaCentralizerValuationBoundary
canonicalP2InertiaCentralizerValuationBoundary =
  p2-inertia-centralizer-valuation-boundary
    true true true true true true true false false
