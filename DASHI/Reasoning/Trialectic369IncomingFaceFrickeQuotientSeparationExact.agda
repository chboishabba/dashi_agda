module DASHI.Reasoning.Trialectic369IncomingFaceFrickeQuotientSeparationExact where

------------------------------------------------------------------------
-- INCOMING FACE QUOTIENT <-> FINITE FRICKE QUOTIENT COORDINATE
--
-- DASHI CONTRIBUTION
--
-- The participant-centered incoming T^2 inversion and the existing finite
-- Fricke completion involution both produce five-state quotient coordinates.
--
-- Their quotient carriers are exactly recharted:
--
--   centre + four unoriented face directions
--      <-> NineOrbit
--      <-> ComplementMode5.
--
-- But the RAW involutions are not the same action:
--
--   * T^2 simultaneous inversion has one fixed point (the centre)
--     and four two-cycles;
--   * the ten-state finite Fricke completion involution has five two-cycles
--     and no fixed point.
--
-- Therefore the five-way quotient-coordinate match does not license an
-- equivariant identification of the raw involutive carriers.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)

import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Biology.NonaryCompletionPhaseQuotientExact as Modes
import DASHI.Biology.ModularCoarseFineAddressFibrationExact as Fricke
import DASHI.Wikimedia.IbrahimMonsterTernary27PhasePreservingFiveOrbitReductionExact as Reduction
import DASHI.Reasoning.Trialectic369IncomingPairFaceDirectionQuotientExact as Incoming

------------------------------------------------------------------------
-- 1. Exact five-state quotient-coordinate rechart.
------------------------------------------------------------------------

faceOrbitToFrickeMode :
  Incoming.FaceOrbit5 ->
  Modes.ComplementMode5
faceOrbitToFrickeMode orbit =
  Reduction.orbitToComplementMode
    (Incoming.faceOrbitToNineOrbit orbit)

frickeModeToFaceOrbit :
  Modes.ComplementMode5 ->
  Incoming.FaceOrbit5
frickeModeToFaceOrbit mode =
  Incoming.nineOrbitToFaceOrbit
    (Reduction.complementModeToOrbit mode)

faceFrickeModeRoundTrip :
  (orbit : Incoming.FaceOrbit5) ->
  frickeModeToFaceOrbit
    (faceOrbitToFrickeMode orbit)
  ≡ orbit
faceFrickeModeRoundTrip orbit =
  trans
    (cong Incoming.nineOrbitToFaceOrbit
      (Reduction.orbitModeRoundTrip
        (Incoming.faceOrbitToNineOrbit orbit)))
    (Incoming.faceNineOrbitRoundTrip orbit)

frickeModeFaceRoundTrip :
  (mode : Modes.ComplementMode5) ->
  faceOrbitToFrickeMode
    (frickeModeToFaceOrbit mode)
  ≡ mode
frickeModeFaceRoundTrip mode =
  trans
    (cong Reduction.orbitToComplementMode
      (Incoming.nineFaceOrbitRoundTrip
        (Reduction.complementModeToOrbit mode)))
    (Reduction.modeOrbitRoundTrip mode)

------------------------------------------------------------------------
-- 2. Incoming quotient mode and finite Fricke mode are the same TYPE of
--    quotient coordinate, but arise from different raw carriers.
------------------------------------------------------------------------

incomingQuotientMode :
  Triadic.NineSheet ->
  Modes.ComplementMode5
incomingQuotientMode sheet =
  faceOrbitToFrickeMode
    (Incoming.nineSheetFaceOrbit sheet)

incomingQuotientAgreesWithGenericNineOrbit :
  (sheet : Triadic.NineSheet) ->
  incomingQuotientMode sheet
  ≡
  Reduction.orbitToComplementMode
    (Triadic.quotientNine sheet)
incomingQuotientAgreesWithGenericNineOrbit sheet =
  cong
    Reduction.orbitToComplementMode
    (sym
      (Incoming.genericQuotientAgreesWithFaceDirectionQuotient
        sheet))

finiteFrickeMode :
  Modes.DecimalCompletionState ->
  Modes.ComplementMode5
finiteFrickeMode =
  Fricke.finiteHauptmodulCoordinate

finiteFrickeModeInvariant :
  (state : Modes.DecimalCompletionState) ->
  finiteFrickeMode
    (Fricke.finiteFrickeSector state)
  ≡ finiteFrickeMode state
finiteFrickeModeInvariant =
  Fricke.finiteHauptmodulFrickeInvariant

------------------------------------------------------------------------
-- 3. The incoming inversion has a fixed centre.
------------------------------------------------------------------------

incomingCentre :
  Triadic.NineSheet
incomingCentre =
  Triadic.kZero , Triadic.kZero

incomingCentreFixed :
  Triadic.negateNine incomingCentre
  ≡ incomingCentre
incomingCentreFixed = refl

------------------------------------------------------------------------
-- 4. The ten-state finite Fricke involution has no fixed state.
------------------------------------------------------------------------

finiteFrickeNoFixedPoint :
  (state : Modes.DecimalCompletionState) ->
  Fricke.finiteFrickeSector state ≡ state ->
  ⊥
finiteFrickeNoFixedPoint Modes.d0 ()
finiteFrickeNoFixedPoint Modes.d1 ()
finiteFrickeNoFixedPoint Modes.d2 ()
finiteFrickeNoFixedPoint Modes.d3 ()
finiteFrickeNoFixedPoint Modes.d4 ()
finiteFrickeNoFixedPoint Modes.d5 ()
finiteFrickeNoFixedPoint Modes.d6 ()
finiteFrickeNoFixedPoint Modes.d7 ()
finiteFrickeNoFixedPoint Modes.d8 ()
finiteFrickeNoFixedPoint Modes.j9 ()

------------------------------------------------------------------------
-- 5. Any raw equivariant bijection would transport the incoming fixed point to
--    a finite-Fricke fixed point, contradiction.
------------------------------------------------------------------------

record RawInvolutionEquivariantBijection : Set where
  field
    toFricke :
      Triadic.NineSheet ->
      Modes.DecimalCompletionState

    fromFricke :
      Modes.DecimalCompletionState ->
      Triadic.NineSheet

    fromAfterTo :
      (sheet : Triadic.NineSheet) ->
      fromFricke (toFricke sheet) ≡ sheet

    toAfterFrom :
      (state : Modes.DecimalCompletionState) ->
      toFricke (fromFricke state) ≡ state

    intertwinesInvolution :
      (sheet : Triadic.NineSheet) ->
      toFricke (Triadic.negateNine sheet)
      ≡ Fricke.finiteFrickeSector (toFricke sheet)

open RawInvolutionEquivariantBijection public

rawEquivariantBijectionImpossible :
  RawInvolutionEquivariantBijection ->
  ⊥
rawEquivariantBijectionImpossible recognition =
  finiteFrickeNoFixedPoint
    (toFricke recognition incomingCentre)
    fixed
  where
    fixed :
      Fricke.finiteFrickeSector
        (toFricke recognition incomingCentre)
      ≡ toFricke recognition incomingCentre
    fixed =
      trans
        (sym
          (intertwinesInvolution recognition incomingCentre))
        (cong
          (toFricke recognition)
          incomingCentreFixed)

------------------------------------------------------------------------
-- 5b. Orbit counts agree but stabilizer profiles do not.
--
-- For a C2 involution, a fixed point has stabilizer size 2 and a non-fixed
-- two-cycle has stabilizer size 1.  The incoming quotient therefore has
--
--   (2,1,1,1,1)
--
-- while every finite-Fricke mode comes from a free two-cycle:
--
--   (1,1,1,1,1).
------------------------------------------------------------------------

incomingOrbitStabilizerSize :
  Incoming.FaceOrbit5 ->
  Nat
incomingOrbitStabilizerSize Incoming.centreOrbit = 2
incomingOrbitStabilizerSize Incoming.horizontalOrbit = 1
incomingOrbitStabilizerSize Incoming.verticalOrbit = 1
incomingOrbitStabilizerSize Incoming.positiveDiagonalOrbit = 1
incomingOrbitStabilizerSize Incoming.negativeDiagonalOrbit = 1

finiteFrickeModeStabilizerSize :
  Modes.ComplementMode5 ->
  Nat
finiteFrickeModeStabilizerSize Modes.mode09 = 1
finiteFrickeModeStabilizerSize Modes.mode18 = 1
finiteFrickeModeStabilizerSize Modes.mode27 = 1
finiteFrickeModeStabilizerSize Modes.mode36 = 1
finiteFrickeModeStabilizerSize Modes.mode45 = 1

record StabilizerPreservingFiveWayRecognition : Set where
  field
    toMode :
      Incoming.FaceOrbit5 ->
      Modes.ComplementMode5

    fromMode :
      Modes.ComplementMode5 ->
      Incoming.FaceOrbit5

    fromAfterTo :
      (orbit : Incoming.FaceOrbit5) ->
      fromMode (toMode orbit) ≡ orbit

    toAfterFrom :
      (mode : Modes.ComplementMode5) ->
      toMode (fromMode mode) ≡ mode

    stabilizerSizePreserved :
      (orbit : Incoming.FaceOrbit5) ->
      incomingOrbitStabilizerSize orbit
      ≡ finiteFrickeModeStabilizerSize (toMode orbit)

open StabilizerPreservingFiveWayRecognition public

stabilizerPreservingFiveWayRecognitionImpossible :
  StabilizerPreservingFiveWayRecognition ->
  ⊥
stabilizerPreservingFiveWayRecognitionImpossible recognition
  with toMode recognition Incoming.centreOrbit
     | stabilizerSizePreserved recognition Incoming.centreOrbit
... | Modes.mode09 | ()
... | Modes.mode18 | ()
... | Modes.mode27 | ()
... | Modes.mode36 | ()
... | Modes.mode45 | ()

------------------------------------------------------------------------
-- 6. Recognition consequence.
------------------------------------------------------------------------

data QuotientCoordinateMatchImpliesRawActionIdentity : Set where
data FiniteFrickeModelIsAnalyticFricke : Set where

quotientMatchDoesNotPromoteRawActionIdentity :
  QuotientCoordinateMatchImpliesRawActionIdentity -> ⊥
quotientMatchDoesNotPromoteRawActionIdentity ()

finiteFrickeStillNotPromotedToAnalyticFricke :
  FiniteFrickeModelIsAnalyticFricke -> ⊥
finiteFrickeStillNotPromotedToAnalyticFricke ()

record Trialectic369IncomingFaceFrickeQuotientSeparationBoundary : Set where
  constructor trialectic-369-incoming-face-fricke-quotient-separation-boundary
  field
    faceOrbitFrickeModeBidiPaid : Bool
    incomingQuotientModeAgreesWithNineOrbit : Bool
    finiteFrickeModeInvariantOwned : Bool
    incomingRawInversionHasFixedCentre : Bool
    finiteFrickeRawInvolutionFixedPointFree : Bool
    rawEquivariantBijectionRejected : Bool
    incomingOrbitStabilizerProfileTwoOneOneOneOne : Bool
    finiteFrickeStabilizerProfileAllOne : Bool
    stabilizerPreservingFiveWayRecognitionRejected : Bool
    quotientCoordinateMatchPromotesRawActionIdentity : Bool
    analyticFrickeIdentificationPaid : Bool

canonicalTrialectic369IncomingFaceFrickeQuotientSeparationBoundary :
  Trialectic369IncomingFaceFrickeQuotientSeparationBoundary
canonicalTrialectic369IncomingFaceFrickeQuotientSeparationBoundary =
  trialectic-369-incoming-face-fricke-quotient-separation-boundary
    true true true true true true
    true true true
    false false
