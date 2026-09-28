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
    quotientCoordinateMatchPromotesRawActionIdentity : Bool
    analyticFrickeIdentificationPaid : Bool

canonicalTrialectic369IncomingFaceFrickeQuotientSeparationBoundary :
  Trialectic369IncomingFaceFrickeQuotientSeparationBoundary
canonicalTrialectic369IncomingFaceFrickeQuotientSeparationBoundary =
  trialectic-369-incoming-face-fricke-quotient-separation-boundary
    true true true true true true false false
