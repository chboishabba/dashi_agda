module DASHI.Moonshine.P11FullLevel2RigidificationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Nicholas M. Katz and Barry Mazur,
-- "Arithmetic Moduli of Elliptic Curves", Annals of Mathematics Studies 108,
-- Princeton University Press, 1985.
-- DOI: 10.1515/9781400881710.
--
-- Fred Diamond and Jerry Shurman,
-- "A First Course in Modular Forms", Graduate Texts in Mathematics 228,
-- Springer, 2005.
-- DOI: 10.1007/978-0-387-27226-9.
--
-- John Voight,
-- "Quaternion Algebras", Graduate Texts in Mathematics 288, Springer, 2021.
-- DOI: 10.1007/978-3-030-56694-4.
-- Chapter 42 DOI: 10.1007/978-3-030-56694-4_42.
--
-- SOURCE ROLE
--
-- Away from characteristic 2, a full level-2 structure is an ordered basis of
-- E[2], hence the frame torsor has six elements with change-of-frame group
-- GL_2(F_2) ~= S_3.  At p=11 the two supersingular classes have reduced
-- automorphism orders 3 (j=0) and 2 (j=1728).  Modding the six frames by those
-- free reduced-automorphism actions therefore gives 6/3=2 and 6/2=3 rigidified
-- classes.
--
-- DASHI CONTRIBUTION
--
-- Encode one explicit regular S3 presentation on the six frames.  The order-3
-- and order-2 left actions satisfy the S3 relation s r s = r^-1.  Their free
-- orbit quotients give exactly two j=0 sheets and three j=1728 sheets, and that
-- five-element rigidified carrier is identified with the existing positive
-- carrier A0,A1,B0,B1,B2.
--
-- IMPORTANT BOUNDARY
--
-- This module does NOT yet construct the Hecke action on full level-2 moduli.
-- Ordinary T_ell is prime-to-level compatible for odd ell; ell=2 divides the
-- auxiliary level and must not be silently treated as the same correspondence.
-- The S3 here is the full-level-2 change-of-frame group; it is NOT identified
-- with PR #558's ternary-pants/tree S3 without an explicit action map.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.P11GeometricSupersingularCarrierExact as Geo
import DASHI.Moonshine.P11FiveStatePositiveHeckeLiftExact as Fine5
import DASHI.Moonshine.P11EichlerDeuringStackUnweightingExact as Stack11

------------------------------------------------------------------------
-- A concrete six-element regular S3 frame torsor.
--
-- Label the elements e,r,r^2,s,sr^2,sr respectively as f0,...,f5.  Then left
-- multiplication by r and s is represented below.
------------------------------------------------------------------------

data Level2Frame : Set where
  f0 f1 f2 f3 f4 f5 : Level2Frame

leftR : Level2Frame → Level2Frame
leftR f0 = f1
leftR f1 = f2
leftR f2 = f0
leftR f3 = f4
leftR f4 = f5
leftR f5 = f3

leftR3IsIdentity : (x : Level2Frame) → leftR (leftR (leftR x)) ≡ x
leftR3IsIdentity f0 = refl
leftR3IsIdentity f1 = refl
leftR3IsIdentity f2 = refl
leftR3IsIdentity f3 = refl
leftR3IsIdentity f4 = refl
leftR3IsIdentity f5 = refl

leftRHasNoFixedFrame : (x : Level2Frame) → leftR x ≡ x → ⊥
leftRHasNoFixedFrame f0 ()
leftRHasNoFixedFrame f1 ()
leftRHasNoFixedFrame f2 ()
leftRHasNoFixedFrame f3 ()
leftRHasNoFixedFrame f4 ()
leftRHasNoFixedFrame f5 ()

leftS : Level2Frame → Level2Frame
leftS f0 = f3
leftS f3 = f0
leftS f1 = f5
leftS f5 = f1
leftS f2 = f4
leftS f4 = f2

leftS2IsIdentity : (x : Level2Frame) → leftS (leftS x) ≡ x
leftS2IsIdentity f0 = refl
leftS2IsIdentity f1 = refl
leftS2IsIdentity f2 = refl
leftS2IsIdentity f3 = refl
leftS2IsIdentity f4 = refl
leftS2IsIdentity f5 = refl

leftSHasNoFixedFrame : (x : Level2Frame) → leftS x ≡ x → ⊥
leftSHasNoFixedFrame f0 ()
leftSHasNoFixedFrame f1 ()
leftSHasNoFixedFrame f2 ()
leftSHasNoFixedFrame f3 ()
leftSHasNoFixedFrame f4 ()
leftSHasNoFixedFrame f5 ()

leftSRSIsRInverse :
  (x : Level2Frame) → leftS (leftR (leftS x)) ≡ leftR (leftR x)
leftSRSIsRInverse f0 = refl
leftSRSIsRInverse f1 = refl
leftSRSIsRInverse f2 = refl
leftSRSIsRInverse f3 = refl
leftSRSIsRInverse f4 = refl
leftSRSIsRInverse f5 = refl

------------------------------------------------------------------------
-- Explicit quotient orbit carriers.
------------------------------------------------------------------------

data J0Level2Orbit : Set where
  j0Orbit0 j0Orbit1 : J0Level2Orbit

j0OrbitOfFrame : Level2Frame → J0Level2Orbit
j0OrbitOfFrame f0 = j0Orbit0
j0OrbitOfFrame f1 = j0Orbit0
j0OrbitOfFrame f2 = j0Orbit0
j0OrbitOfFrame f3 = j0Orbit1
j0OrbitOfFrame f4 = j0Orbit1
j0OrbitOfFrame f5 = j0Orbit1

j0OrbitInvariantUnderReducedAut :
  (x : Level2Frame) → j0OrbitOfFrame (leftR x) ≡ j0OrbitOfFrame x
j0OrbitInvariantUnderReducedAut f0 = refl
j0OrbitInvariantUnderReducedAut f1 = refl
j0OrbitInvariantUnderReducedAut f2 = refl
j0OrbitInvariantUnderReducedAut f3 = refl
j0OrbitInvariantUnderReducedAut f4 = refl
j0OrbitInvariantUnderReducedAut f5 = refl

data J1728Level2Orbit : Set where
  j1728Orbit0 j1728Orbit1 j1728Orbit2 : J1728Level2Orbit

j1728OrbitOfFrame : Level2Frame → J1728Level2Orbit
j1728OrbitOfFrame f0 = j1728Orbit0
j1728OrbitOfFrame f3 = j1728Orbit0
j1728OrbitOfFrame f1 = j1728Orbit1
j1728OrbitOfFrame f5 = j1728Orbit1
j1728OrbitOfFrame f2 = j1728Orbit2
j1728OrbitOfFrame f4 = j1728Orbit2

j1728OrbitInvariantUnderReducedAut :
  (x : Level2Frame) → j1728OrbitOfFrame (leftS x) ≡ j1728OrbitOfFrame x
j1728OrbitInvariantUnderReducedAut f0 = refl
j1728OrbitInvariantUnderReducedAut f1 = refl
j1728OrbitInvariantUnderReducedAut f2 = refl
j1728OrbitInvariantUnderReducedAut f3 = refl
j1728OrbitInvariantUnderReducedAut f4 = refl
j1728OrbitInvariantUnderReducedAut f5 = refl

------------------------------------------------------------------------
-- The actual five rigidified characteristic-11 classes.
------------------------------------------------------------------------

data P11Level2Rigidified : Set where
  atJ0 : J0Level2Orbit → P11Level2Rigidified
  atJ1728 : J1728Level2Orbit → P11Level2Rigidified

forgetLevel2 : P11Level2Rigidified → Geo.P11SupersingularJ
forgetLevel2 (atJ0 _) = Geo.jZeroSS
forgetLevel2 (atJ1728 _) = Geo.j1728SS

------------------------------------------------------------------------
-- Exact identification with the existing positive five-state carrier.
------------------------------------------------------------------------

toFine5 : P11Level2Rigidified → Fine5.P11Fine5
toFine5 (atJ0 j0Orbit0) = Fine5.a0
toFine5 (atJ0 j0Orbit1) = Fine5.a1
toFine5 (atJ1728 j1728Orbit0) = Fine5.b0
toFine5 (atJ1728 j1728Orbit1) = Fine5.b1
toFine5 (atJ1728 j1728Orbit2) = Fine5.b2

fromFine5 : Fine5.P11Fine5 → P11Level2Rigidified
fromFine5 Fine5.a0 = atJ0 j0Orbit0
fromFine5 Fine5.a1 = atJ0 j0Orbit1
fromFine5 Fine5.b0 = atJ1728 j1728Orbit0
fromFine5 Fine5.b1 = atJ1728 j1728Orbit1
fromFine5 Fine5.b2 = atJ1728 j1728Orbit2

fromAfterTo : (x : P11Level2Rigidified) → fromFine5 (toFine5 x) ≡ x
fromAfterTo (atJ0 j0Orbit0) = refl
fromAfterTo (atJ0 j0Orbit1) = refl
fromAfterTo (atJ1728 j1728Orbit0) = refl
fromAfterTo (atJ1728 j1728Orbit1) = refl
fromAfterTo (atJ1728 j1728Orbit2) = refl

toAfterFrom : (x : Fine5.P11Fine5) → toFine5 (fromFine5 x) ≡ x
toAfterFrom Fine5.a0 = refl
toAfterFrom Fine5.a1 = refl
toAfterFrom Fine5.b0 = refl
toAfterFrom Fine5.b1 = refl
toAfterFrom Fine5.b2 = refl

forgetLevel2MatchesFineProjection :
  (x : P11Level2Rigidified) →
  Fine5.projectFine5 (toFine5 x) ≡ forgetLevel2 x
forgetLevel2MatchesFineProjection (atJ0 j0Orbit0) = refl
forgetLevel2MatchesFineProjection (atJ0 j0Orbit1) = refl
forgetLevel2MatchesFineProjection (atJ1728 j1728Orbit0) = refl
forgetLevel2MatchesFineProjection (atJ1728 j1728Orbit1) = refl
forgetLevel2MatchesFineProjection (atJ1728 j1728Orbit2) = refl

------------------------------------------------------------------------
-- Orbit counts recover the stack-unweighting multiplicities definitionally.
------------------------------------------------------------------------

j0RigidifiedOrbitCount : Nat
j0RigidifiedOrbitCount = 2

j1728RigidifiedOrbitCount : Nat
j1728RigidifiedOrbitCount = 3

j0OrbitCountMatchesStackMultiplicity :
  j0RigidifiedOrbitCount ≡ Stack11.p11SheetMultiplicity Geo.jZeroSS
j0OrbitCountMatchesStackMultiplicity = refl

j1728OrbitCountMatchesStackMultiplicity :
  j1728RigidifiedOrbitCount ≡ Stack11.p11SheetMultiplicity Geo.j1728SS
j1728OrbitCountMatchesStackMultiplicity = refl

p11FullLevel2RigidifiedCount : Nat
p11FullLevel2RigidifiedCount = j0RigidifiedOrbitCount + j1728RigidifiedOrbitCount

p11FullLevel2RigidifiedCountIsFive : p11FullLevel2RigidifiedCount ≡ 5
p11FullLevel2RigidifiedCountIsFive = refl

p11FullLevel2CountMatchesStackUnweighting :
  p11FullLevel2RigidifiedCount ≡ Stack11.p11UnweightedStateCount
p11FullLevel2CountMatchesStackUnweighting = refl

------------------------------------------------------------------------
-- Boundary: this identifies the carrier geometry, not yet the Hecke action.
------------------------------------------------------------------------

record P11FullLevel2RigidificationBoundary : Set where
  field
    commonSixFrameTorsorConstructed : Bool
    commonSixFrameTorsorConstructedIsTrue :
      commonSixFrameTorsorConstructed ≡ true

    regularS3RelationsConstructed : Bool
    regularS3RelationsConstructedIsTrue : regularS3RelationsConstructed ≡ true

    reducedC3ActionHasTwoFreeOrbits : Bool
    reducedC3ActionHasTwoFreeOrbitsIsTrue :
      reducedC3ActionHasTwoFreeOrbits ≡ true

    reducedC2ActionHasThreeFreeOrbits : Bool
    reducedC2ActionHasThreeFreeOrbitsIsTrue :
      reducedC2ActionHasThreeFreeOrbits ≡ true

    rigidifiedCarrierIdentifiedWithExistingFine5 : Bool
    rigidifiedCarrierIdentifiedWithExistingFine5IsTrue :
      rigidifiedCarrierIdentifiedWithExistingFine5 ≡ true

    oddPrimeHeckeActionOnLevel2CarrierConstructedHere : Bool
    oddPrimeHeckeActionOnLevel2CarrierConstructedHereIsFalse :
      oddPrimeHeckeActionOnLevel2CarrierConstructedHere ≡ false

    ell2TreatedAsPrimeToLevelHeckeOperator : Bool
    ell2TreatedAsPrimeToLevelHeckeOperatorIsFalse :
      ell2TreatedAsPrimeToLevelHeckeOperator ≡ false

    ternaryPantsS3IdentifiedWithLevel2FrameS3 : Bool
    ternaryPantsS3IdentifiedWithLevel2FrameS3IsFalse :
      ternaryPantsS3IdentifiedWithLevel2FrameS3 ≡ false

canonicalP11FullLevel2RigidificationBoundary :
  P11FullLevel2RigidificationBoundary
canonicalP11FullLevel2RigidificationBoundary =
  record
    { commonSixFrameTorsorConstructed = true
    ; commonSixFrameTorsorConstructedIsTrue = refl
    ; regularS3RelationsConstructed = true
    ; regularS3RelationsConstructedIsTrue = refl
    ; reducedC3ActionHasTwoFreeOrbits = true
    ; reducedC3ActionHasTwoFreeOrbitsIsTrue = refl
    ; reducedC2ActionHasThreeFreeOrbits = true
    ; reducedC2ActionHasThreeFreeOrbitsIsTrue = refl
    ; rigidifiedCarrierIdentifiedWithExistingFine5 = true
    ; rigidifiedCarrierIdentifiedWithExistingFine5IsTrue = refl
    ; oddPrimeHeckeActionOnLevel2CarrierConstructedHere = false
    ; oddPrimeHeckeActionOnLevel2CarrierConstructedHereIsFalse = refl
    ; ell2TreatedAsPrimeToLevelHeckeOperator = false
    ; ell2TreatedAsPrimeToLevelHeckeOperatorIsFalse = refl
    ; ternaryPantsS3IdentifiedWithLevel2FrameS3 = false
    ; ternaryPantsS3IdentifiedWithLevel2FrameS3IsFalse = refl
    }
