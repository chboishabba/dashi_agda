module DASHI.Moonshine.OggSSP15PhaseOrbitC3EquivarianceExact where

------------------------------------------------------------------------
-- C3 EQUIVARIANCE OF THE CHOSEN 3 x 5 SSP15 PRESENTATION
--
-- DASHI CONTRIBUTION
--
-- The structural phase-orbit carrier
--
--   PhaseOrbit15 = outer ternary phase x five inner inversion orbits
--
-- has a canonical order-three action on the OUTER ternary phase, leaving the
-- inner orbit fixed.
--
-- Via the exact chosen Ogg <-> PhaseOrbit15 bidi, this transports to an exact
-- order-three permutation of the fifteen Ogg lanes.
--
-- Important distinction:
-- the existing SSP affine +12/+42 C3 acts on THREE MOBILE COMPLEMENT MODES,
-- i.e. on an inner-mode coordinate.  It is therefore not silently identified
-- with this outer-phase C3.  We prove the coordinate separation explicitly.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Moonshine.OggSSP15PhaseOrbitBidiExact as Bidi
import DASHI.Moonshine.SSP15AffineC3TranslationExact as Affine
import DASHI.Wikimedia.IbrahimMonsterTernary27PhasePreservingFiveOrbitReductionExact as Reduction
import DASHI.Biology.NonaryCompletionPhaseQuotientExact as Modes
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane

------------------------------------------------------------------------
-- 1. Outer-phase C3.
------------------------------------------------------------------------

advanceOuterPhase :
  SSP.SSPTrit ->
  SSP.SSPTrit
advanceOuterPhase SSP.sspNegOne = SSP.sspZero
advanceOuterPhase SSP.sspZero = SSP.sspPosOne
advanceOuterPhase SSP.sspPosOne = SSP.sspNegOne

advanceOuterPhaseCubed :
  (phase : SSP.SSPTrit) ->
  advanceOuterPhase
    (advanceOuterPhase
      (advanceOuterPhase phase))
  ≡ phase
advanceOuterPhaseCubed SSP.sspNegOne = refl
advanceOuterPhaseCubed SSP.sspZero = refl
advanceOuterPhaseCubed SSP.sspPosOne = refl

advancePhaseOrbit :
  Bidi.PhaseOrbit15 ->
  Bidi.PhaseOrbit15
advancePhaseOrbit (phase , orbit) =
  advanceOuterPhase phase , orbit

advancePhaseOrbitCubed :
  (state : Bidi.PhaseOrbit15) ->
  advancePhaseOrbit
    (advancePhaseOrbit
      (advancePhaseOrbit state))
  ≡ state
advancePhaseOrbitCubed (phase , orbit)
  rewrite advanceOuterPhaseCubed phase = refl

phaseOrbitAdvancePreservesInnerOrbit :
  (state : Bidi.PhaseOrbit15) ->
  proj₂ (advancePhaseOrbit state) ≡ proj₂ state
phaseOrbitAdvancePreservesInnerOrbit (phase , orbit) = refl

------------------------------------------------------------------------
-- 2. Transport the C3 action through the chosen Ogg bidi.
------------------------------------------------------------------------

advanceChosenOggPresentation :
  Bidi.OggSSP15Lane ->
  Bidi.OggSSP15Lane
advanceChosenOggPresentation prime =
  Bidi.phaseOrbit15ToOgg
    (advancePhaseOrbit
      (Bidi.oggToPhaseOrbit15 prime))

oggBidiIntertwinesPresentationC3 :
  (prime : Bidi.OggSSP15Lane) ->
  Bidi.oggToPhaseOrbit15
    (advanceChosenOggPresentation prime)
  ≡
  advancePhaseOrbit
    (Bidi.oggToPhaseOrbit15 prime)
oggBidiIntertwinesPresentationC3 prime =
  Bidi.phaseOrbitAfterOgg
    (advancePhaseOrbit
      (Bidi.oggToPhaseOrbit15 prime))

advanceChosenOggPresentationCubed :
  (prime : Bidi.OggSSP15Lane) ->
  advanceChosenOggPresentation
    (advanceChosenOggPresentation
      (advanceChosenOggPresentation prime))
  ≡ prime
advanceChosenOggPresentationCubed prime =
  trans
    (cong
      Bidi.phaseOrbit15ToOgg
      (advancePhaseOrbitCubed
        (Bidi.oggToPhaseOrbit15 prime)))
    (Bidi.oggAfterPhaseOrbit prime)

------------------------------------------------------------------------
-- 3. Concrete chosen C3 triples.
------------------------------------------------------------------------

presentationP2ToP3 :
  advanceChosenOggPresentation Lane.p2 ≡ Lane.p3
presentationP2ToP3 = refl

presentationP3ToP5 :
  advanceChosenOggPresentation Lane.p3 ≡ Lane.p5
presentationP3ToP5 = refl

presentationP5ToP2 :
  advanceChosenOggPresentation Lane.p5 ≡ Lane.p2
presentationP5ToP2 = refl

presentationP47ToP59 :
  advanceChosenOggPresentation Lane.p47 ≡ Lane.p59
presentationP47ToP59 = refl

presentationP59ToP71 :
  advanceChosenOggPresentation Lane.p59 ≡ Lane.p71
presentationP59ToP71 = refl

presentationP71ToP47 :
  advanceChosenOggPresentation Lane.p71 ≡ Lane.p47
presentationP71ToP47 = refl

------------------------------------------------------------------------
-- 4. Coordinate separation from the existing affine SSP C3.
--
-- The chosen outer-phase action keeps the inner orbit fixed.
-- The affine +12/+42 action changes one of the mobile complement modes.
------------------------------------------------------------------------

chosenPrimeInnerMode :
  Bidi.OggSSP15Lane ->
  Modes.ComplementMode5
chosenPrimeInnerMode prime =
  Reduction.orbitToComplementMode
    (proj₂ (Bidi.oggToPhaseOrbit15 prime))

presentationC3PreservesChosenInnerMode :
  (prime : Bidi.OggSSP15Lane) ->
  chosenPrimeInnerMode
    (advanceChosenOggPresentation prime)
  ≡
  chosenPrimeInnerMode prime
presentationC3PreservesChosenInnerMode prime =
  cong
    Reduction.orbitToComplementMode
    (cong proj₂
      (oggBidiIntertwinesPresentationC3 prime))

affineAdvance12MovesMobile45 :
  Affine.advance12 Affine.mobile45
  ≡ Affine.mobile18
affineAdvance12MovesMobile45 = refl

affineAdvance42MovesMobile45 :
  Affine.advance42 Affine.mobile45
  ≡ Affine.mobile27
affineAdvance42MovesMobile45 = refl

data PresentationOuterC3EqualsAffineMobileModeC3 : Set where

outerPhaseC3NotPromotedToAffineModeC3 :
  PresentationOuterC3EqualsAffineMobileModeC3 -> ⊥
outerPhaseC3NotPromotedToAffineModeC3 ()

------------------------------------------------------------------------
-- 5. Boundary.
------------------------------------------------------------------------

record OggSSP15PhaseOrbitC3EquivarianceBoundary : Set where
  constructor ogg-ssp15-phase-orbit-c3-equivariance-boundary
  field
    outerPhaseC3Owned : Bool
    outerPhaseC3OrderThree : Bool
    chosenOggPresentationActionOwned : Bool
    chosenOggBidiIntertwinesOuterC3 : Bool
    chosenInnerOrbitPreserved : Bool
    affineMobileModeC3Reused : Bool
    affineMobileModeC3MovesInnerMode : Bool
    outerPhaseC3IdentifiedWithAffineModeC3 : Bool

canonicalOggSSP15PhaseOrbitC3EquivarianceBoundary :
  OggSSP15PhaseOrbitC3EquivarianceBoundary
canonicalOggSSP15PhaseOrbitC3EquivarianceBoundary =
  ogg-ssp15-phase-orbit-c3-equivariance-boundary
    true true true true true true true false
