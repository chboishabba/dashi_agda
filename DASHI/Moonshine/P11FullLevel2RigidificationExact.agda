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
-- Encode the exact finite quotient geometry explicitly and identify its five
-- orbit classes with the already-constructed positive carrier
--
--   A0,A1,B0,B1,B2.
--
-- This is stronger than a mass/cardinality receipt: the two and three sheets
-- are represented as actual quotient orbits of one common six-frame S3 torsor.
--
-- IMPORTANT BOUNDARY
--
-- This module does NOT yet construct the Hecke action on full level-2 moduli.
-- In particular, the ordinary prime-to-level T_ell correspondence is naturally
-- compatible with full level 2 for odd ell; ell=2 divides the auxiliary level
-- and must not be silently identified with the same T_2 correspondence.
-- The S3 here is the full-level-2 change-of-frame group; it is NOT identified
-- with PR #558's ternary-pants/tree S3 without an explicit action map.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.P11GeometricSupersingularCarrierExact as Geo
import DASHI.Moonshine.P11FiveStatePositiveHeckeLiftExact as Fine5
import DASHI.Moonshine.P11EichlerDeuringStackUnweightingExact as Stack11

------------------------------------------------------------------------
-- A concrete six-element regular S3 frame torsor.
------------------------------------------------------------------------

data Level2Frame : Set where
  f0 f1 f2 f3 f4 f5 : Level2Frame

-- Left multiplication by an order-3 element in one explicit regular-action
-- presentation.  It has two free orbits of size three.

c3Step : Level2Frame → Level2Frame
c3Step f0 = f1
c3Step f1 = f2
c3Step f2 = f0
c3Step f3 = f4
c3Step f4 = f5
c3Step f5 = f3

c3Step3IsIdentity : (x : Level2Frame) → c3Step (c3Step (c3Step x)) ≡ x
c3Step3IsIdentity f0 = refl
c3Step3IsIdentity f1 = refl
c3Step3IsIdentity f2 = refl
c3Step3IsIdentity f3 = refl
c3Step3IsIdentity f4 = refl
c3Step3IsIdentity f5 = refl

c3StepHasNoFixedFrame : (x : Level2Frame) → c3Step x ≡ x → ⊥
c3StepHasNoFixedFrame f0 ()
c3StepHasNoFixedFrame f1 ()
c3StepHasNoFixedFrame f2 ()
c3StepHasNoFixedFrame f3 ()
c3StepHasNoFixedFrame f4 ()
c3StepHasNoFixedFrame f5 ()

-- Left multiplication by an order-2 element.  It has three free orbits of
-- size two.

c2Step : Level2Frame → Level2Frame
c2Step f0 = f1
c2Step f1 = f0
c2Step f2 = f3
c2Step f3 = f2
c2Step f4 = f5
c2Step f5 = f4

c2Step2IsIdentity : (x : Level2Frame) → c2Step (c2Step x) ≡ x
c2Step2IsIdentity f0 = refl
c2Step2IsIdentity f1 = refl
c2Step2IsIdentity f2 = refl
c2Step2IsIdentity f3 = refl
c2Step2IsIdentity f4 = refl
c2Step2IsIdentity f5 = refl

c2StepHasNoFixedFrame : (x : Level2Frame) → c2Step x ≡ x → ⊥
c2StepHasNoFixedFrame f0 ()
c2StepHasNoFixedFrame f1 ()
c2StepHasNoFixedFrame f2 ()
c2StepHasNoFixedFrame f3 ()
c2StepHasNoFixedFrame f4 ()
c2StepHasNoFixedFrame f5 ()

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

j0OrbitInvariantUnderC3 :
  (x : Level2Frame) → j0OrbitOfFrame (c3Step x) ≡ j0OrbitOfFrame x
j0OrbitInvariantUnderC3 f0 = refl
j0OrbitInvariantUnderC3 f1 = refl
j0OrbitInvariantUnderC3 f2 = refl
j0OrbitInvariantUnderC3 f3 = refl
j0OrbitInvariantUnderC3 f4 = refl
j0OrbitInvariantUnderC3 f5 = refl

data J1728Level2Orbit : Set where
  j1728Orbit0 j1728Orbit1 j1728Orbit2 : J1728Level2Orbit

j1728OrbitOfFrame : Level2Frame → J1728Level2Orbit
j1728OrbitOfFrame f0 = j1728Orbit0
j1728OrbitOfFrame f1 = j1728Orbit0
j1728OrbitOfFrame f2 = j1728Orbit1
j1728OrbitOfFrame f3 = j1728Orbit1
j1728OrbitOfFrame f4 = j1728Orbit2
j1728OrbitOfFrame f5 = j1728Orbit2

j1728OrbitInvariantUnderC2 :
  (x : Level2Frame) → j1728OrbitOfFrame (c2Step x) ≡ j1728OrbitOfFrame x
j1728OrbitInvariantUnderC2 f0 = refl
j1728OrbitInvariantUnderC2 f1 = refl
j1728OrbitInvariantUnderC2 f2 = refl
j1728OrbitInvariantUnderC2 f3 = refl
j1728OrbitInvariantUnderC2 f4 = refl
j1728OrbitInvariantUnderC2 f5 = refl

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
