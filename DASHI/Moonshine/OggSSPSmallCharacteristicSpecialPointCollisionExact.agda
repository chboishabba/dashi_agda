module DASHI.Moonshine.OggSSPSmallCharacteristicSpecialPointCollisionExact where

------------------------------------------------------------------------
-- SMALL-CHARACTERISTIC j=0 / j=1728 SPECIAL-POINT COLLISION
--
-- EXTERNAL DUNCAN--SWISHER INPUT
--
-- Proposition 3.1 distinguishes the two exceptional supersingular locations:
--
--   J_1 = -744   <-> j = 0,
--   J_1 =  984   <-> j = 1728,
--
-- because the Legendre local parameter has cubic behaviour at j=0 and
-- quadratic behaviour at j=1728.
--
-- Table 2 then shows that for p=2 and p=3 the SAME supersingular residue
-- representative 0 occurs in both special columns.
--
-- DASHI FORMAL RECONSTRUCTION
--
-- The collision is the literal arithmetic fact
--
--   1728 == 0 mod 2,
--   1728 == 0 mod 3.
--
-- Thus the two tame exceptional local roles live over one residue point at the
-- wild primes.  This is a source-grounded common geometric anomaly.
--
-- FIREWALL
--
-- The collision does NOT by itself prove the missing Monster corrections 10/2
-- or construct an exceptional fourth-term valuation.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_%_)

import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution
import DASHI.Moonshine.OggSSPSmallCharacteristicClassicalSourceAtlasExact as Classical

------------------------------------------------------------------------
-- 1. Literal collision at p=2,3.
------------------------------------------------------------------------

jZero : Nat
jZero = 0

jSpecial : Nat
jSpecial = 1728

jZeroModTwo :
  jZero % 2 ≡ 0
jZeroModTwo = refl

j1728ModTwo :
  jSpecial % 2 ≡ 0
j1728ModTwo = refl

jZeroModThree :
  jZero % 3 ≡ 0
jZeroModThree = refl

j1728ModThree :
  jSpecial % 3 ≡ 0
j1728ModThree = refl

p2SpecialJResiduesCollide :
  jZero % 2 ≡ jSpecial % 2
p2SpecialJResiduesCollide = refl

p3SpecialJResiduesCollide :
  jZero % 3 ≡ jSpecial % 3
p3SpecialJResiduesCollide = refl

------------------------------------------------------------------------
-- 2. The two source-side local roles remain semantically distinct.
------------------------------------------------------------------------

data ExceptionalLocalRole : Set where
  cubicJZeroRole :
    ExceptionalLocalRole
  quadraticJ1728Role :
    ExceptionalLocalRole

data WildPrime : Set where
  wildTwo wildThree : WildPrime

record CollidedSpecialPoint : Set where
  constructor collided-special-point
  field
    prime :
      WildPrime

    residueRepresentative :
      Nat

    carriesCubicRole :
      Bool

    carriesQuadraticRole :
      Bool

open CollidedSpecialPoint public

p2CollidedSpecialPoint :
  CollidedSpecialPoint
p2CollidedSpecialPoint =
  collided-special-point
    wildTwo
    0
    true
    true

p3CollidedSpecialPoint :
  CollidedSpecialPoint
p3CollidedSpecialPoint =
  collided-special-point
    wildThree
    0
    true
    true

------------------------------------------------------------------------
-- 3. Collision is a geometric/source anomaly, not yet a valuation payment.
------------------------------------------------------------------------

data SpecialPointCollisionExplainsP2MonsterGap : Set where
data SpecialPointCollisionExplainsP3MonsterGap : Set where
data CubicQuadraticRoleCollisionCreatesFourthTerm : Set where
data DuncanSwisherProvedCollisionCorrection : Set where

collisionDoesNotYetExplainP2MonsterGap :
  SpecialPointCollisionExplainsP2MonsterGap -> ⊥
collisionDoesNotYetExplainP2MonsterGap ()

collisionDoesNotYetExplainP3MonsterGap :
  SpecialPointCollisionExplainsP3MonsterGap -> ⊥
collisionDoesNotYetExplainP3MonsterGap ()

collisionDoesNotConstructFourthTerm :
  CubicQuadraticRoleCollisionCreatesFourthTerm -> ⊥
collisionDoesNotConstructFourthTerm ()

duncanSwisherNotCreditedWithCollisionCorrection :
  DuncanSwisherProvedCollisionCorrection -> ⊥
duncanSwisherNotCreditedWithCollisionCorrection ()

classicalBoundary :
  Classical.SmallCharacteristicClassicalSourcingBoundary
classicalBoundary =
  Classical.canonicalSmallCharacteristicClassicalSourcingBoundary

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryFormalReconstruction

record SpecialPointCollisionBoundary : Set where
  constructor special-point-collision-boundary
  field
    p2JZeroJ1728CollisionExact : Bool
    p3JZeroJ1728CollisionExact : Bool
    cubicAndQuadraticSourceRolesRetained : Bool
    sameResidueCarriesBothRolesAtP2 : Bool
    sameResidueCarriesBothRolesAtP3 : Bool
    collisionPromotedToMonsterCorrection : Bool
    collisionPromotedToFourthTerm : Bool
    attributionFirewallPreserved : Bool

canonicalSpecialPointCollisionBoundary :
  SpecialPointCollisionBoundary
canonicalSpecialPointCollisionBoundary =
  special-point-collision-boundary
    true true true true true false false true
