module DASHI.Moonshine.Base369Monster3BGlobalNineToOnePlusTwoPlusSixBidiExact where

------------------------------------------------------------------------
-- GLOBAL MONSTER / BASE369 REFACTOR:
--
--   9 = 1 + 8 = 1 + 2 + 6
--
-- The existing Base369 primary bulk is
--
--   10 * 3^9 = 196830.
--
-- The certified 3B character restriction gives the same bulk as
--
--   3 * 65610,
--
-- while the nontrivial central phase has
--
--   65610 = 90 * 729 = (10 * 3^2) * 3^6.
--
-- Hence the exact nested arithmetic/carrier shadow is
--
--   10 * 3^9
--     = 3 * (10 * 3^8)
--     = 3 * (10 * 3^2) * 3^6
--     = 3 * 90 * 729.
--
-- IMPORTANT TYPE BOUNDARY:
-- the outer factor 3 is a genuine regular-C3 CHARACTER coordinate.  The
-- 729 x 90 Stone-von-Neumann structure is literal for the nontrivial zeta and
-- zeta^2 phases only.  The fixed phase has the same regular-bulk DIMENSION but
-- central-trivial representation type and must be analysed through E/Z(E).
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_; _+_)

import DASHI.Moonshine.Base369MonsterTwoComponentCompletionBidiExact as Two
import DASHI.Moonshine.Monster3BRegularC3BulkResidualFiftyThreeBidiExact as Regular
import DASHI.Moonshine.Monster3BMultiplicityEvaluationExact as Multiplicity
import DASHI.Moonshine.Base369Monster3BMultiplicityCompletedTenTritSquareCompilerExact as Ninety
import DASHI.Moonshine.Base369MonsterThreeLocalEightToSixPlusTwoCarrierBidiExact as EightSixTwo
import DASHI.Moonshine.Monster3BFixedPhaseAbelianQuotientCorrectionBidiExact as Fixed

------------------------------------------------------------------------
-- 1. Exact nested dimensions.
------------------------------------------------------------------------

oneRegularPhaseDimension : Nat
oneRegularPhaseDimension = 10 * 6561

oneRegularPhaseDimensionIs65610 : oneRegularPhaseDimension ≡ 65610
oneRegularPhaseDimensionIs65610 = refl

oneRegularPhaseAsTenTimesThreeToEight : 10 * 6561 ≡ 65610
oneRegularPhaseAsTenTimesThreeToEight = refl

oneRegularPhaseAsNinetyTimes729 : 90 * 729 ≡ 65610
oneRegularPhaseAsNinetyTimes729 = refl

oneRegularPhaseAsTenTimesNineTimes729 : 10 * 9 * 729 ≡ 65610
oneRegularPhaseAsTenTimesNineTimes729 = refl

regularThreePhaseBulkDimension : Nat
regularThreePhaseBulkDimension = 3 * oneRegularPhaseDimension

regularThreePhaseBulkIs196830 : regularThreePhaseBulkDimension ≡ 196830
regularThreePhaseBulkIs196830 = refl

base369PrimaryAgreesWithThreePhaseBulk :
  Two.primary369Component Two.reducedMonsterTwoComponent
  ≡ regularThreePhaseBulkDimension
base369PrimaryAgreesWithThreePhaseBulk = refl

monsterReducedGlobal : regularThreePhaseBulkDimension + 53 ≡ 196883
monsterReducedGlobal = refl

------------------------------------------------------------------------
-- 2. Exponent decomposition receipts.
--
-- These are arithmetic/carrier shadows, not assertions that all factors carry
-- identical actions.
------------------------------------------------------------------------

threeToNine : Nat
threeToNine = 19683

threeToEight : Nat
threeToEight = 6561

threeToSix : Nat
threeToSix = 729

threeToTwo : Nat
threeToTwo = 9

nineAsOnePlusEight : threeToNine ≡ 3 * threeToEight
nineAsOnePlusEight = refl

eightAsTwoPlusSix : threeToEight ≡ threeToTwo * threeToSix
eightAsTwoPlusSix = refl

nineAsOnePlusTwoPlusSix :
  threeToNine ≡ 3 * threeToTwo * threeToSix
nineAsOnePlusTwoPlusSix = refl

tenTimesNineAsPhaseTimesCompletedTritSquareTimesX6 :
  10 * threeToNine ≡ 3 * (10 * threeToTwo) * threeToSix
tenTimesNineAsPhaseTimesCompletedTritSquareTimesX6 = refl

------------------------------------------------------------------------
-- 3. Global semantic stratification.
------------------------------------------------------------------------

record GlobalNineStratificationBoundary : Set where
  constructor globalNineStratificationBoundary
  field
    base369PrimaryTenTimesThreeToNineOwned : Bool
    certifiedRegularC3BulkThreeTimes65610Owned : Bool
    nontrivialPhase65610Is729Times90Target : Bool
    ninetyCarrierIsCompleted10TimesTritSquareGenerated : Bool
    threeToEightCarrierSplitsAsThreeToSixTimesThreeToTwo : Bool
    exponentNineEqualsOnePlusTwoPlusSix : Bool
    outerThreeHasCertifiedC3CharacterMeaning : Bool
    zeta729Times90HasStoneVonNeumannMeaning : Bool
    zetaSquared729Times90HasStoneVonNeumannMeaning : Bool
    fixedPhase729Times90HasStoneVonNeumannMeaning : Bool
    fixedPhaseRequiresAbelianQuotientAnalysis : Bool
    residual53StillSeparateSameActionLift : Bool

canonicalGlobalNineStratificationBoundary : GlobalNineStratificationBoundary
canonicalGlobalNineStratificationBoundary =
  globalNineStratificationBoundary
    true true true true true true
    true true true
    false true true

------------------------------------------------------------------------
-- 4. Implication.
--
-- The numerical identity
--
--   196830 = 10 * 3^9
--
-- is now simultaneously:
--
--   * the original completed Base369 9-trit bulk;
--   * the exact regular-C3 character bulk 3 * 65610;
--   * two literal nontrivial phase modules of shape
--         T^6 x (Completed10 x T^2),
--     plus one fixed-phase block of equal dimension but different E-type.
--
-- Thus the full construction is not three identical 65610 representations.
-- It is one regular-C3 character package whose nontrivial phases admit the
-- Heisenberg 6+2 refinement and whose trivial phase demands quotient-character
-- analysis.  The 53 lives entirely as the excess trivial-phase multiplicity.
------------------------------------------------------------------------
