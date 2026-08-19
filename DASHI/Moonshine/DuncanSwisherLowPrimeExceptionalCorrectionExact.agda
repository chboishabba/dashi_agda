module DASHI.Moonshine.DuncanSwisherLowPrimeExceptionalCorrectionExact where

------------------------------------------------------------------------
-- LOW-PRIME EXCEPTIONAL CORRECTION: COMPARISON, NOT CAUSAL PROMOTION
--
-- PRIMARY SOURCE
-- John F. R. Duncan and Holly Swisher,
-- "Modular Functions and the Monstrous Exponents", 2026.
-- arXiv:2602.09135. DOI: 10.48550/arXiv.2602.09135.
--
-- GROUP-THEORETIC SOURCE
-- Conway, Curtis, Norton, Parker, Wilson,
-- "Atlas of Finite Groups", Oxford University Press, 1985.
-- ISBN 0-19-853199-0; no DOI asserted.
--
-- What is now known on the same comparison surface:
--
--   p=2 : Duncan--Swisher common RHS 36 + correction 10 = 46
--         = full Monster 2-local depth;
--   p=3 : Duncan--Swisher common RHS 18 + correction  2 = 20
--         = full Monster 3-local depth.
--
-- Independently, the special j=0 and j=1728 residue roles collide in exactly
-- these two characteristics.  Remark 1.4's Faber/V_p observer applies to every
-- prime, so it is a candidate all-prime multiplicity-unit observer.
--
-- NONE of those statements proves that the corrections 10 and 2 are wild
-- ramification, inertia, stack, or a named subgroup factor.  This file keeps the
-- neutral name `exceptionalCorrection` until such a causal bridge is derived.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.DuncanSwisherLowPrimeResidualExact as Low
import DASHI.Moonshine.DuncanSwisherLowPrimeEllipticCollisionExact as Collision
import DASHI.Moonshine.MonsterLowPrimeLocalSubgroupDepthExact as Local
import DASHI.Moonshine.DuncanSwisherFaberVpDepthExact as Faber

exceptionalCorrection : Low.DuncanSwisherLowPrime → Nat
exceptionalCorrection = Low.lowPrimeResidual

p2ExceptionalCorrectionIsTen : exceptionalCorrection Low.low2 ≡ 10
p2ExceptionalCorrectionIsTen = Low.p2ResidualIsTen

p3ExceptionalCorrectionIsTwo : exceptionalCorrection Low.low3 ≡ 2
p3ExceptionalCorrectionIsTwo = Low.p3ResidualIsTwo

p2ComparisonClosesExactly :
  Low.commonDuncanSwisherRHS Low.low2 + exceptionalCorrection Low.low2
  ≡ Local.twoBLocalTwoDepth
p2ComparisonClosesExactly = Local.p2RHSPlusResidualEqualsLocalDepth

p3ComparisonClosesExactly :
  Low.commonDuncanSwisherRHS Low.low3 + exceptionalCorrection Low.low3
  ≡ Local.threeBLocalThreeDepth
p3ComparisonClosesExactly = Local.p3RHSPlusResidualEqualsLocalDepth

p2EllipticRolesCollapseAtSourceSurface :
  Collision.specialResidueRepresentative Low.low2 Collision.jZeroRole
  ≡ Collision.specialResidueRepresentative Low.low2 Collision.j1728Role
p2EllipticRolesCollapseAtSourceSurface = Collision.lowPrimeSpecialResiduesCollide Low.low2

p3EllipticRolesCollapseAtSourceSurface :
  Collision.specialResidueRepresentative Low.low3 Collision.jZeroRole
  ≡ Collision.specialResidueRepresentative Low.low3 Collision.j1728Role
p3EllipticRolesCollapseAtSourceSurface = Collision.lowPrimeSpecialResiduesCollide Low.low3

-- Remark 1.4 is represented by the all-prime Faber authority surface.  We do
-- not need to fabricate concrete Prime 2/Prime 3 proofs here merely to record
-- the theorem-boundary fact that the Faber lane itself is not p>3-restricted.
faberObserverTheorem12LowPrimePromotionBlocked :
  Faber.theoremCoversTwoAndThreeThroughTheorem12
    Faber.canonicalDuncanSwisherFaberVpDepthBoundary ≡ false
faberObserverTheorem12LowPrimePromotionBlocked = refl

record DuncanSwisherLowPrimeExceptionalCorrectionBoundary : Set where
  field
    correctionsTenAndTwoExact : Bool
    localMonsterDepthClosesBothComparisons : Bool
    ellipticResidueCollisionExposedAtBothPrimes : Bool
    faberMultiplicityUnitAvailableAllPrimeAtSource : Bool
    theorem12PromotedToTwoAndThree : Bool
    correctionIdentifiedAsWildRamification : Bool
    correctionIdentifiedAsNamedLocalSubgroupFactor : Bool
    causalBridgeFromEllipticCollisionToCorrectionProved : Bool

canonicalDuncanSwisherLowPrimeExceptionalCorrectionBoundary :
  DuncanSwisherLowPrimeExceptionalCorrectionBoundary
canonicalDuncanSwisherLowPrimeExceptionalCorrectionBoundary = record
  { correctionsTenAndTwoExact = true
  ; localMonsterDepthClosesBothComparisons = true
  ; ellipticResidueCollisionExposedAtBothPrimes = true
  ; faberMultiplicityUnitAvailableAllPrimeAtSource = true
  ; theorem12PromotedToTwoAndThree = false
  ; correctionIdentifiedAsWildRamification = false
  ; correctionIdentifiedAsNamedLocalSubgroupFactor = false
  ; causalBridgeFromEllipticCollisionToCorrectionProved = false
  }
