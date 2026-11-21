module DASHI.Analysis.RHGRHPrimeE8Punctured27MonsterCMSourceCutExact where

-- Use the ACTUAL original source owners. No inferred representation,
-- global analytic theta equality, supersingular-field interpretation,
-- or original automorphic Hecke TLiftK witness.
--
-- The five-orbit / thirteen-axis are DIFFERENT quotient constructions:
-- NineSheet / inversion is 5 states; punctured F3^3 / antipode is 13.
-- The second carries a reconstructible orientation bit and a native
-- spatial four-cycle holonomy obstruction.
-- Monster 196884 decomposition is literally SOURCE-OWNED, not a
-- representation or analytic j/zeta equality.
-- E8 roots = first Bishop E4 coefficient only; theta_E8=E4 all-q OPEN.
--
-- Source-written Agda; kernel validation OPEN, no CI.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)

import DASHI.Moonshine.Monster196884FibreInterferenceExact as Monster
import DASHI.Moonshine.JInvariant369Zeta6561MonsterCrosswalkExact as J
import DASHI.Moonshine.AbelE8RootE4FirstCoefficientExact as E8
import DASHI.Unified.HyperfabricPunctured27Projective13OrientationExact as P13
import DASHI.Moonshine.Base369P2FiveOrbitOrientationGroupoidsExact as Five
import DASHI.Moonshine.SupersingularFrobeniusOrbitSpectrumExact as SS
import DASHI.Moonshine.MonsterOrderExponentCorrectionExact as MonsterOrder
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as PrimeLane
import DASHI.Analysis.RHGRHCubicCharacterCMTOEConsumerExact as TOE
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Cube
import DASHI.Algebra.Trit.E8RootEnumeration as Roots
import DASHI.Moonshine.JInvariantEisensteinIncrementCoefficientBoundExact as E4
import DASHI.Moonshine.OggPrimeControlMatrixExact as Matrix

-- First-class original dimension/trace consumers. These source symbols
-- represent genuinely different typed proof statements, not inferred aliases.
monsterFineCoarseExact :
  Monster.fibreInterferenceTotal ≡ 196884
monsterFineCoarseExact = Monster.fibreInterferenceTotalIs196884

monsterFiveTwoTimesThreePowerNine :
  Monster.fineSectorDimension ≡ 196830
monsterFiveTwoTimesThreePowerNine = Monster.fineSectorDimensionIs196830

monsterSixTimesNineCoarse :
  Monster.coarseSectorDimension ≡ 54
monsterSixTimesNineCoarse = Monster.coarseSectorDimensionIs54

monsterFinePlusCoarse :
  196830 + 54 ≡ 196884
monsterFinePlusCoarse = Monster.finePlusCoarseIdentity

monsterFactorizedOriginal :
  (5 * 2) * 19683 + (3 * 2) * (3 * 3) ≡ 196884
monsterFactorizedOriginal = refl

monsterDistinctRegularBulk :
  196830 ≡ 3 * 65610
monsterDistinctRegularBulk = J.oneNineSixEightThreeZeroIsThreeTimes65610

monsterThreeBRegularCopies :
  65610 ≡ 90 * 729
monsterThreeBRegularCopies = J.sixFiveSixOneZeroIsNinetyTimes729

-- On the actual 27-point original chart, only the native origin is
-- punctured. The order-2 orientation is preserved, not projected away.
nativeOriginNotEncoded :
  P13.encode
    Cube.origin
    ≡ nothing
nativeOriginNotEncoded = P13.originExcluded

nativeAxisOrientationRoundTrip :
  (a : P13.Axis13) (orientation : Bool) →
  P13.encode (P13.decode (a , orientation))
    ≡ just (a , orientation)
nativeAxisOrientationRoundTrip = P13.decodeEncode

nativeThirteenSupportSplit : 13 ≡ 3 + 6 + 4
nativeThirteenSupportSplit = P13.exactThirteenBySupport

nativeTwentySixAsOrientedThirteen : 26 ≡ 2 * 13
nativeTwentySixAsOrientedThirteen = P13.twoOrientedForEachUnoriented

-- This is the actual native selected adjacency obstruction, rather
-- than a claim that point-set encoding preserves every graph edge.
nativeFourCycleNoGlobalOrientation :
  (x pp y pm : Bool) →
  P13._xor_ x pp ≡ false →
  P13._xor_ pp y ≡ false →
  P13._xor_ y pm ≡ true →
  P13._xor_ pm x ≡ false → ⊥
nativeFourCycleNoGlobalOrientation =
  P13.noEdgeCompatibleOrientation

-- Genuine E8 / Bishop E4 first-term arithmetic, not all-q theta identity.
e8FirstE4CoefficientExact :
  Roots.indexedRootListLength
    Roots.combinedIndexedRoots
  ≡
  E4.e4IncrementCoefficient 0
e8FirstE4CoefficientExact = E8.originalE8RootListEqualsE4FirstCoefficient

-- p=5 is a real Monster prime lane with order valuation 9.
monsterP5PrimaryExponentNine :
  MonsterOrder.monsterOrderExponent PrimeLane.p5 ≡ 9
monsterP5PrimaryExponentNine = MonsterOrder.p5ExponentIsNine

-- Prime-specific supersingular orbit spectrum requires individual source
-- Fricke rows and is NOT the ten-prime p≡1 mod 3 regression sample.
primeFiveSupersingularOrbitAccounting :
  SS.totalSupersingularCount
    Matrix.prime5
  ≡
  SS.rationalSupersingularCount
    Matrix.prime5
    + 2 * SS.frobeniusTwoOrbitCount
      Matrix.prime5
primeFiveSupersingularOrbitAccounting =
  SS.supersingularOrbitCountExact
    Matrix.prime5

-- This source file deliberately has no map to the original CM
-- global Hecke character, full E8 theta, or RH analytic zero owner.
