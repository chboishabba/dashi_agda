module DASHI.Moonshine.P11MarkedHeckeThetaCollisionCriterionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- John Voight,
-- "Quaternion Algebras", Graduate Texts in Mathematics 288, Springer, 2021.
-- DOI: 10.1007/978-3-030-56694-4.
--
-- Jean-Pierre Serre,
-- "A Course in Arithmetic", Springer, 1973.
-- DOI: 10.1007/978-1-4684-9884-4.
--
-- DASHI CONTRIBUTION
--
-- Compress the p=11 marked Brandt-newform/deck-standard collision to ONE
-- arithmetic theta identity.
--
-- Write d = ell+1 and let t be the integral cross-orbital multiplicity, so the
-- coarse two-state Brandt row shape is
--
--   [[d-3t, 3t],
--    [2t,   d-2t]].
--
-- Its nonconstant eigenvalue is d-5t.  Avoid subtraction by representing a
-- signed integer as a pair (positive,negative), modulo
--
--   (p,n) ~ (p',n')  iff  p+n' = p'+n.
--
-- Thus the coarse nonconstant eigenvalue is represented by
--
--   (d, 4t+t),
--
-- while the B-fibre deck-standard eigenvalue is represented by
--
--   (bb_id, t)
--
-- whenever bb_off=t.  The single marked theta identity
--
--   bb_id + 4t = d
--
-- then proves equality of the two signed differences.
--
-- At ell=3,5,7 the source-native quaternion computations satisfy this exactly.
-- The executable scan in scripts/verify_p11_marked_hecke_collision_scan.py
-- checks the same identity at every odd prime through 47 except 11, but that
-- finite scan is NOT promoted to the all-prime theorem.
--
-- Therefore the live global producer is now precise:
-- prove the marked j=1728 theta coefficient identity bb_id(ell)+4t(ell)=ell+1
-- for every prime-to-22 Hecke prime (or identify the correct modular theta
-- statement implying it).
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.P11MarkedQuaternionThetaExact as Theta35
import DASHI.Moonshine.P11MarkedQuaternionThetaEll7Exact as Theta7

------------------------------------------------------------------------
-- Subtraction-free signed differences.
------------------------------------------------------------------------

record NatDifference : Set where
  constructor natDifference
  field
    positive negative : Nat

open NatDifference public

DifferenceEquivalent : NatDifference → NatDifference → Set
DifferenceEquivalent x y =
  positive x + negative y ≡ positive y + negative x

coarseNonconstantDifference : Nat → Nat → NatDifference
coarseNonconstantDifference degree crossUnit =
  natDifference degree ((4 * crossUnit) + crossUnit)

standardDeckDifference : Nat → Nat → NatDifference
standardDeckDifference bbIdentity crossUnit =
  natDifference bbIdentity crossUnit

------------------------------------------------------------------------
-- One theta identity forces equality of the two eigenvalue differences.
------------------------------------------------------------------------

thetaIdentityForcesDeckBrandtCollision :
  (degree crossUnit bbIdentity : Nat) →
  bbIdentity + (4 * crossUnit) ≡ degree →
  DifferenceEquivalent
    (standardDeckDifference bbIdentity crossUnit)
    (coarseNonconstantDifference degree crossUnit)
thetaIdentityForcesDeckBrandtCollision degree crossUnit bbIdentity thetaIdentity =
  trans
    (sym (+-assoc bbIdentity (4 * crossUnit) crossUnit))
    (cong (λ z → z + crossUnit) thetaIdentity)

------------------------------------------------------------------------
-- Exact source-native instances at ell=3,5,7.
------------------------------------------------------------------------

ell3ThetaCollisionIdentity :
  Theta35.j1728MarkedT3LoopCount + (4 * 1) ≡ 4
ell3ThetaCollisionIdentity = refl

ell5ThetaCollisionIdentity :
  Theta35.j1728MarkedT5LoopCount + (4 * 1) ≡ 6
ell5ThetaCollisionIdentity = refl

ell7ThetaCollisionIdentity :
  Theta7.j1728MarkedT7LoopCount + (4 * 2) ≡ 8
ell7ThetaCollisionIdentity = refl

ell3DeckBrandtDifferenceCollision :
  DifferenceEquivalent
    (standardDeckDifference Theta35.j1728MarkedT3LoopCount 1)
    (coarseNonconstantDifference 4 1)
ell3DeckBrandtDifferenceCollision =
  thetaIdentityForcesDeckBrandtCollision 4 1 Theta35.j1728MarkedT3LoopCount
    ell3ThetaCollisionIdentity

ell5DeckBrandtDifferenceCollision :
  DifferenceEquivalent
    (standardDeckDifference Theta35.j1728MarkedT5LoopCount 1)
    (coarseNonconstantDifference 6 1)
ell5DeckBrandtDifferenceCollision =
  thetaIdentityForcesDeckBrandtCollision 6 1 Theta35.j1728MarkedT5LoopCount
    ell5ThetaCollisionIdentity

ell7DeckBrandtDifferenceCollision :
  DifferenceEquivalent
    (standardDeckDifference Theta7.j1728MarkedT7LoopCount 2)
    (coarseNonconstantDifference 8 2)
ell7DeckBrandtDifferenceCollision =
  thetaIdentityForcesDeckBrandtCollision 8 2 Theta7.j1728MarkedT7LoopCount
    ell7ThetaCollisionIdentity

record P11MarkedHeckeThetaCollisionBoundary : Set where
  field
    collisionReducedToOneThetaIdentity : Bool
    collisionReducedToOneThetaIdentityIsTrue :
      collisionReducedToOneThetaIdentity ≡ true

    ell3Ell5Ell7InstancesConstructed : Bool
    ell3Ell5Ell7InstancesConstructedIsTrue :
      ell3Ell5Ell7InstancesConstructed ≡ true

    finiteScanPromotedToAllPrimeProof : Bool
    finiteScanPromotedToAllPrimeProofIsFalse :
      finiteScanPromotedToAllPrimeProof ≡ false

    globalThetaIdentityStillOpen : Bool
    globalThetaIdentityStillOpenIsTrue : globalThetaIdentityStillOpen ≡ true

canonicalP11MarkedHeckeThetaCollisionBoundary :
  P11MarkedHeckeThetaCollisionBoundary
canonicalP11MarkedHeckeThetaCollisionBoundary = record
  { collisionReducedToOneThetaIdentity = true
  ; collisionReducedToOneThetaIdentityIsTrue = refl
  ; ell3Ell5Ell7InstancesConstructed = true
  ; ell3Ell5Ell7InstancesConstructedIsTrue = refl
  ; finiteScanPromotedToAllPrimeProof = false
  ; finiteScanPromotedToAllPrimeProofIsFalse = refl
  ; globalThetaIdentityStillOpen = true
  ; globalThetaIdentityStillOpenIsTrue = refl
  }
