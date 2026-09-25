module DASHI.Moonshine.OggSSPSmallCharacteristicExceptionalJCollisionExact where

------------------------------------------------------------------------
-- SMALL-CHARACTERISTIC COLLISION OF THE TWO EXCEPTIONAL ELLIPTIC LOCI
--
-- Duncan--Swisher / Deligne-Dwork setup distinguishes:
--
--   beta_0 : j = 0      (J_1 = -744), cubic local ramification;
--   beta_1 : j = 1728   (J_1 =  984), quadratic local ramification.
--
-- For p > 3 these are distinct exceptional residue classes whenever both are
-- present.  At p=2 and p=3 they collide:
--
--   -744 == 984 == 0  (mod p).
--
-- Duncan--Swisher Table 2 records exactly this: the two exceptional columns
-- are both represented by 0 at p=2 and p=3.
--
-- Their singleton supersingular statistic then retains only
--
--   m_2 = 24,  m_3 = 12,
--
-- and the tame-shaped 3/2*m_p continuation gives 36 and 18.
--
-- This module records the collision as a structural diagnostic.  It does NOT
-- prove that resolving the collision supplies the Monster corrections 10,2.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Nat using (_%_)

import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane
import DASHI.Moonshine.MonsterOrderExponentCorrectionExact as Exponent
import DASHI.Moonshine.OggSSPSmallCharacteristicClassicalSourceAtlasExact as Classical
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Literal exceptional J_1 representatives.
------------------------------------------------------------------------

-- J_1 = j - 744.
-- For j=0, a nonnegative representative modulo p can be computed from 744.
-- For j=1728, J_1=984.

betaZeroIntegerMagnitude : Nat
betaZeroIntegerMagnitude = 744

betaOneInteger : Nat
betaOneInteger = 984

-- Equivalent collision test: 1728 = 984 + 744 vanishes modulo p.
jDifference : Nat
jDifference = 1728

p2JDifferenceVanishes :
  jDifference % 2 ≡ 0
p2JDifferenceVanishes = refl

p3JDifferenceVanishes :
  jDifference % 3 ≡ 0
p3JDifferenceVanishes = refl

p2BetaZeroRepresentative :
  betaZeroIntegerMagnitude % 2 ≡ 0
p2BetaZeroRepresentative = refl

p2BetaOneRepresentative :
  betaOneInteger % 2 ≡ 0
p2BetaOneRepresentative = refl

p3BetaZeroRepresentative :
  betaZeroIntegerMagnitude % 3 ≡ 0
p3BetaZeroRepresentative = refl

p3BetaOneRepresentative :
  betaOneInteger % 3 ≡ 0
p3BetaOneRepresentative = refl

------------------------------------------------------------------------
-- 2. Distinct tame local roles collide at one small-prime coarse point.
------------------------------------------------------------------------

data ExceptionalLocalRole : Set where
  cubicJZeroRole :
    ExceptionalLocalRole
  quadraticJ1728Role :
    ExceptionalLocalRole

data SmallPrime : Set where
  p2 p3 : SmallPrime

data CollidedExceptionalPoint : Set where
  collidedZeroResidue :
    CollidedExceptionalPoint

exceptionalResidue :
  SmallPrime ->
  ExceptionalLocalRole ->
  CollidedExceptionalPoint
exceptionalResidue p2 cubicJZeroRole = collidedZeroResidue
exceptionalResidue p2 quadraticJ1728Role = collidedZeroResidue
exceptionalResidue p3 cubicJZeroRole = collidedZeroResidue
exceptionalResidue p3 quadraticJ1728Role = collidedZeroResidue

p2ExceptionalRolesCollide :
  exceptionalResidue p2 cubicJZeroRole
  ≡
  exceptionalResidue p2 quadraticJ1728Role
p2ExceptionalRolesCollide = refl

p3ExceptionalRolesCollide :
  exceptionalResidue p3 cubicJZeroRole
  ≡
  exceptionalResidue p3 quadraticJ1728Role
p3ExceptionalRolesCollide = refl

data CollisionMeansRolesSemanticallyIdentical : Set where

collisionDoesNotEraseDistinctLocalRoles :
  CollisionMeansRolesSemanticallyIdentical -> ⊥
collisionDoesNotEraseDistinctLocalRoles ()

------------------------------------------------------------------------
-- 3. Duncan--Swisher small-prime automorphism statistic.
------------------------------------------------------------------------

minimumAutomorphismOrder : SmallPrime -> Nat
minimumAutomorphismOrder p2 = 24
minimumAutomorphismOrder p3 = 12

-- Avoid division in the executable surface: 3/2*m_p is integral here.
threeHalvesAutomorphismStatistic : SmallPrime -> Nat
threeHalvesAutomorphismStatistic p2 = 36
threeHalvesAutomorphismStatistic p3 = 18

p2StatisticMatchesDuncanSwisherContinuation :
  threeHalvesAutomorphismStatistic p2
  ≡
  Exponent.duncanSwisherExceptionalRHS Lane.p2
p2StatisticMatchesDuncanSwisherContinuation = refl

p3StatisticMatchesDuncanSwisherContinuation :
  threeHalvesAutomorphismStatistic p3
  ≡
  Exponent.duncanSwisherExceptionalRHS Lane.p3
p3StatisticMatchesDuncanSwisherContinuation = refl

p2MonsterExceedsCollapsedStatistic :
  Exponent.monsterOrderExponent Lane.p2
  ≡ threeHalvesAutomorphismStatistic p2 + 10
p2MonsterExceedsCollapsedStatistic =
  Exponent.p2ExceptionalGap

p3MonsterExceedsCollapsedStatistic :
  Exponent.monsterOrderExponent Lane.p3
  ≡ threeHalvesAutomorphismStatistic p3 + 2
p3MonsterExceedsCollapsedStatistic =
  Exponent.p3ExceptionalGap

------------------------------------------------------------------------
-- 4. Collision-resolution conjectural seam.
------------------------------------------------------------------------

data ResolvingExceptionalCollisionProducesMonsterGap : Set where
data AutomorphismOrderAloneRecoversWildInternalMarking : Set where
data TableTwoCollisionProvesSectorCorrection : Set where

collisionResolutionMonsterCorrectionStillOpen :
  ResolvingExceptionalCollisionProducesMonsterGap -> ⊥
collisionResolutionMonsterCorrectionStillOpen ()

automorphismOrderDoesNotRecoverInternalMarking :
  AutomorphismOrderAloneRecoversWildInternalMarking -> ⊥
automorphismOrderDoesNotRecoverWildInternalMarking ()

tableCollisionDoesNotProveSectorCorrection :
  TableTwoCollisionProvesSectorCorrection -> ⊥
tableCollisionDoesNotProveSectorCorrection ()

------------------------------------------------------------------------
-- 5. Source / attribution boundary.
------------------------------------------------------------------------

classicalBoundary :
  Classical.SmallCharacteristicClassicalSourcingBoundary
classicalBoundary =
  Classical.canonicalSmallCharacteristicClassicalSourcingBoundary

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryCrossModuleInference

record ExceptionalJCollisionBoundary : Set where
  constructor exceptional-j-collision-boundary
  field
    cubicJZeroRoleRetained : Bool
    quadraticJ1728RoleRetained : Bool
    p2RolesCollideModuloP : Bool
    p3RolesCollideModuloP : Bool
    p2MinimumAutOrderTwentyFour : Bool
    p3MinimumAutOrderTwelve : Bool
    p2CollapsedStatisticThirtySix : Bool
    p3CollapsedStatisticEighteen : Bool
    p2MonsterGapTen : Bool
    p3MonsterGapTwo : Bool
    collisionRolesIdentifiedSemantically : Bool
    collisionResolutionCorrectionProved : Bool

canonicalExceptionalJCollisionBoundary :
  ExceptionalJCollisionBoundary
canonicalExceptionalJCollisionBoundary =
  exceptional-j-collision-boundary
    true true true true
    true true true true
    true true
    false false
