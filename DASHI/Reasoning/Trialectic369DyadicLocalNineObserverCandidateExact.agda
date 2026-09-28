module DASHI.Reasoning.Trialectic369DyadicLocalNineObserverCandidateExact where

------------------------------------------------------------------------
-- DYADIC T4 LOCAL -> T2 FACE -> PHASE-QUOTIENT NINE CANDIDATE
--
-- DASHI CONTRIBUTION
--
-- A dyadic local has four trits:
--
--   U_AB = (AA, AB, BA, BB).
--
-- The existing ordinary j-coarse phase quotient is exactly a two-trit carrier
--
--   PhaseQuotient9 = TriTruth x TriTruth.
--
-- This module chooses the overlap/self face (AA,BB), projects U_AB to that T2
-- face, and reuses the existing exact SSPTrit/TriTruth codec to produce a
-- genuine nine-state observer candidate.
--
-- This does NOT identify PhaseQuotient9 with the distinct D4/five-mode
-- ModePhaseQuotient9.  The latter bridge is represented as an explicit
-- recognition contract at the bottom of the file.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

import Base369 as Base
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Reasoning.Trialectic369DescentNaturalityExact as Descent
import DASHI.Biology.TernaryPhaseQuotientJCoarseBridgeExact as Coarse
import DASHI.Biology.BalancedTernaryHarmonicCarrierExact as Harmonic
import DASHI.Foundations.TernaryEndomorphismPhaseQuotientExact as Phase
import DASHI.Foundations.Base369FiveModePhaseQuotientExact as Five

------------------------------------------------------------------------
-- 1. Existing exact SSPTrit <-> TriTruth coordinate chart.
------------------------------------------------------------------------

sspToTri : SSP.SSPTrit -> Base.TriTruth
sspToTri SSP.sspNegOne = Base.tri-low
sspToTri SSP.sspZero = Base.tri-mid
sspToTri SSP.sspPosOne = Base.tri-high

triToSSP : Base.TriTruth -> SSP.SSPTrit
triToSSP Base.tri-low = SSP.sspNegOne
triToSSP Base.tri-mid = SSP.sspZero
triToSSP Base.tri-high = SSP.sspPosOne

sspTriRoundTrip :
  (trit : SSP.SSPTrit) ->
  triToSSP (sspToTri trit) ≡ trit
sspTriRoundTrip SSP.sspNegOne = refl
sspTriRoundTrip SSP.sspZero = refl
sspTriRoundTrip SSP.sspPosOne = refl

triSSPRoundTrip :
  (trit : Base.TriTruth) ->
  sspToTri (triToSSP trit) ≡ trit
triSSPRoundTrip Base.tri-low = refl
triSSPRoundTrip Base.tri-mid = refl
triSSPRoundTrip Base.tri-high = refl

------------------------------------------------------------------------
-- 2. Chosen overlap/self T2 face of the AB local.
------------------------------------------------------------------------

ABSelfFace2 : Set
ABSelfFace2 = SSP.SSPTrit × SSP.SSPTrit

observeABSelfFace :
  Descent.ABSection ->
  ABSelfFace2
observeABSelfFace section =
  Descent.aaAB section , Descent.bbAB section

------------------------------------------------------------------------
-- 3. Exact T2 <-> PhaseQuotient9 rechart.
------------------------------------------------------------------------

selfFaceToPhaseQuotient9 :
  ABSelfFace2 ->
  Phase.PhaseQuotient9
selfFaceToPhaseQuotient9 (left , right) =
  sspToTri left , sspToTri right

phaseQuotient9ToSelfFace :
  Phase.PhaseQuotient9 ->
  ABSelfFace2
phaseQuotient9ToSelfFace (left , right) =
  triToSSP left , triToSSP right

selfFacePhaseRoundTrip :
  (face : ABSelfFace2) ->
  phaseQuotient9ToSelfFace
    (selfFaceToPhaseQuotient9 face)
  ≡ face
selfFacePhaseRoundTrip (left , right)
  rewrite sspTriRoundTrip left
        | sspTriRoundTrip right = refl

phaseSelfFaceRoundTrip :
  (phase : Phase.PhaseQuotient9) ->
  selfFaceToPhaseQuotient9
    (phaseQuotient9ToSelfFace phase)
  ≡ phase
phaseSelfFaceRoundTrip (left , right)
  rewrite triSSPRoundTrip left
        | triSSPRoundTrip right = refl

------------------------------------------------------------------------
-- 4. Concrete nine-state observer candidate from a dyadic local.
------------------------------------------------------------------------

observeABPhaseQuotient9 :
  Descent.ABSection ->
  Phase.PhaseQuotient9
observeABPhaseQuotient9 =
  selfFaceToPhaseQuotient9 ∘ observeABSelfFace
  where
    _∘_ :
      {A B C : Set} ->
      (B -> C) ->
      (A -> B) ->
      A -> C
    (f ∘ g) x = f (g x)

observeABBalancedPair :
  Descent.ABSection ->
  Harmonic.BalancedPair
observeABBalancedPair section =
  Coarse.phaseQuotientToBalancedPair
    (observeABPhaseQuotient9 section)

------------------------------------------------------------------------
-- 5. The local observer is intentionally lossy: off-diagonal coordinates are
--    forgotten.  Give a literal collision.
------------------------------------------------------------------------

sameFaceLeft : Descent.ABSection
sameFaceLeft =
  Descent.ab-section
    SSP.sspZero
    SSP.sspNegOne
    SSP.sspZero
    SSP.sspZero

sameFaceRight : Descent.ABSection
sameFaceRight =
  Descent.ab-section
    SSP.sspZero
    SSP.sspPosOne
    SSP.sspZero
    SSP.sspZero

sameFaceObservation :
  observeABPhaseQuotient9 sameFaceLeft
  ≡ observeABPhaseQuotient9 sameFaceRight
sameFaceObservation = refl

sameFaceStatesDistinct :
  sameFaceLeft ≡ sameFaceRight -> ⊥
sameFaceStatesDistinct ()

------------------------------------------------------------------------
-- 6. The remaining nine-to-nine recognition seam.
------------------------------------------------------------------------

record PhaseNineToModeNineRecognition : Set where
  constructor phase-nine-to-mode-nine-recognition
  field
    toMode :
      Phase.PhaseQuotient9 ->
      Five.ModePhaseQuotient9
    toPhase :
      Five.ModePhaseQuotient9 ->
      Phase.PhaseQuotient9

    modeAfterPhase :
      (phase : Phase.PhaseQuotient9) ->
      toPhase (toMode phase) ≡ phase

    phaseAfterMode :
      (mode : Five.ModePhaseQuotient9) ->
      toMode (toPhase mode) ≡ mode

open PhaseNineToModeNineRecognition public

observeABModeNine :
  PhaseNineToModeNineRecognition ->
  Descent.ABSection ->
  Five.ModePhaseQuotient9
observeABModeNine recognition section =
  toMode recognition (observeABPhaseQuotient9 section)

data SharedNineCardinalityCreatesRecognition : Set where

sharedNineCardinalityDoesNotCreateRecognition :
  SharedNineCardinalityCreatesRecognition -> ⊥
sharedNineCardinalityDoesNotCreateRecognition ()

------------------------------------------------------------------------
-- 7. Monster-5 provenance firewall.
------------------------------------------------------------------------

data TrialecticCandidateIsActualMonsterFiveLocalCarrier : Set where
data CandidateNineObserverDischargesMonsterTransportIntertwiner : Set where

trialecticCandidateNotPromotedToActualMonsterFiveLocal :
  TrialecticCandidateIsActualMonsterFiveLocalCarrier -> ⊥
trialecticCandidateNotPromotedToActualMonsterFiveLocal ()

candidateObserverDoesNotDischargeMonsterTransport :
  CandidateNineObserverDischargesMonsterTransportIntertwiner -> ⊥
candidateObserverDoesNotDischargeMonsterTransportIntertwiner ()

record Trialectic369DyadicLocalNineObserverCandidateBoundary : Set where
  constructor trialectic-369-dyadic-local-nine-observer-candidate-boundary
  field
    dyadicLocalProjectsToTwoTritFace : Bool
    twoTritFaceExactlyPhaseQuotient9 : Bool
    localNineObserverConstructed : Bool
    localObserverKnownLossy : Bool
    phaseNineToModeNineRecognitionConstructed : Bool
    actualMonsterFiveLocalCarrierIdentified : Bool
    actualMonsterTransportIntertwinerProved : Bool

canonicalTrialectic369DyadicLocalNineObserverCandidateBoundary :
  Trialectic369DyadicLocalNineObserverCandidateBoundary
canonicalTrialectic369DyadicLocalNineObserverCandidateBoundary =
  trialectic-369-dyadic-local-nine-observer-candidate-boundary
    true true true true false false false
