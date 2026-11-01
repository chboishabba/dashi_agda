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
import DASHI.Reasoning.Trialectic369DyadicC3LocalComplementSymmetryExact as C3
import DASHI.Reasoning.TrialecticObserverMatrix369Exact as Observer

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
-- 4b. Participant-C3 covariance of the chosen two-trit observer face.
------------------------------------------------------------------------

observeBCSelfFace :
  Descent.BCSection ->
  ABSelfFace2
observeBCSelfFace section =
  Descent.bbBC section , Descent.ccBC section

observeCASelfFace :
  Descent.CASection ->
  ABSelfFace2
observeCASelfFace section =
  Descent.ccCA section , Descent.aaCA section

observeBCPhaseQuotient9 :
  Descent.BCSection ->
  Phase.PhaseQuotient9
observeBCPhaseQuotient9 =
  selfFaceToPhaseQuotient9 ∘ observeBCSelfFace
  where
    _∘_ :
      {A B C : Set} ->
      (B -> C) ->
      (A -> B) ->
      A -> C
    (f ∘ g) x = f (g x)

observeCAPhaseQuotient9 :
  Descent.CASection ->
  Phase.PhaseQuotient9
observeCAPhaseQuotient9 =
  selfFaceToPhaseQuotient9 ∘ observeCASelfFace
  where
    _∘_ :
      {A B C : Set} ->
      (B -> C) ->
      (A -> B) ->
      A -> C
    (f ∘ g) x = f (g x)

abObserverAfterRotateIsBCObserver :
  (matrix : Observer.ObserverMatrix3 SSP.SSPTrit) ->
  observeABPhaseQuotient9
    (Descent.restrictAB (C3.rotateABC matrix))
  ≡ observeBCPhaseQuotient9
      (Descent.restrictBC matrix)
abObserverAfterRotateIsBCObserver matrix = refl

abObserverAfterRotateTwiceIsCAObserver :
  (matrix : Observer.ObserverMatrix3 SSP.SSPTrit) ->
  observeABPhaseQuotient9
    (Descent.restrictAB (C3.rotateABCTwice matrix))
  ≡ observeCAPhaseQuotient9
      (Descent.restrictCA matrix)
abObserverAfterRotateTwiceIsCAObserver matrix = refl

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
-- 6b. Canonical ordinary-nine carrier rechart.
--
-- The ordinary balanced-pair order is:
--
--   (--), (-0), (-+), (0-), (00), (0+), (+-), (+0), (++)
--
-- and the five-mode quotient has exactly:
--
--   identity,
--   A2-/A2+,
--   B1-/B1+,
--   B2-/B2+,
--   E-/E+.
--
-- This is a DASHI finite-carrier chart.  It does not claim source-derived
-- D4/Monster semantics for the balanced-pair labels.
------------------------------------------------------------------------

phaseNineToModeNine :
  Phase.PhaseQuotient9 ->
  Five.ModePhaseQuotient9
phaseNineToModeNine (Base.tri-low , Base.tri-low) =
  Five.identityMode
phaseNineToModeNine (Base.tri-low , Base.tri-mid) =
  Five.A2negative
phaseNineToModeNine (Base.tri-low , Base.tri-high) =
  Five.A2positive
phaseNineToModeNine (Base.tri-mid , Base.tri-low) =
  Five.B1negative
phaseNineToModeNine (Base.tri-mid , Base.tri-mid) =
  Five.B1positive
phaseNineToModeNine (Base.tri-mid , Base.tri-high) =
  Five.B2negative
phaseNineToModeNine (Base.tri-high , Base.tri-low) =
  Five.B2positive
phaseNineToModeNine (Base.tri-high , Base.tri-mid) =
  Five.Enegative
phaseNineToModeNine (Base.tri-high , Base.tri-high) =
  Five.Epositive

modeNineToPhaseNine :
  Five.ModePhaseQuotient9 ->
  Phase.PhaseQuotient9
modeNineToPhaseNine Five.identityMode =
  Base.tri-low , Base.tri-low
modeNineToPhaseNine Five.A2negative =
  Base.tri-low , Base.tri-mid
modeNineToPhaseNine Five.A2positive =
  Base.tri-low , Base.tri-high
modeNineToPhaseNine Five.B1negative =
  Base.tri-mid , Base.tri-low
modeNineToPhaseNine Five.B1positive =
  Base.tri-mid , Base.tri-mid
modeNineToPhaseNine Five.B2negative =
  Base.tri-mid , Base.tri-high
modeNineToPhaseNine Five.B2positive =
  Base.tri-high , Base.tri-low
modeNineToPhaseNine Five.Enegative =
  Base.tri-high , Base.tri-mid
modeNineToPhaseNine Five.Epositive =
  Base.tri-high , Base.tri-high

modeAfterPhaseNine :
  (phase : Phase.PhaseQuotient9) ->
  modeNineToPhaseNine (phaseNineToModeNine phase) ≡ phase
modeAfterPhaseNine (Base.tri-low , Base.tri-low) = refl
modeAfterPhaseNine (Base.tri-low , Base.tri-mid) = refl
modeAfterPhaseNine (Base.tri-low , Base.tri-high) = refl
modeAfterPhaseNine (Base.tri-mid , Base.tri-low) = refl
modeAfterPhaseNine (Base.tri-mid , Base.tri-mid) = refl
modeAfterPhaseNine (Base.tri-mid , Base.tri-high) = refl
modeAfterPhaseNine (Base.tri-high , Base.tri-low) = refl
modeAfterPhaseNine (Base.tri-high , Base.tri-mid) = refl
modeAfterPhaseNine (Base.tri-high , Base.tri-high) = refl

phaseAfterModeNine :
  (mode : Five.ModePhaseQuotient9) ->
  phaseNineToModeNine (modeNineToPhaseNine mode) ≡ mode
phaseAfterModeNine Five.identityMode = refl
phaseAfterModeNine Five.A2negative = refl
phaseAfterModeNine Five.A2positive = refl
phaseAfterModeNine Five.B1negative = refl
phaseAfterModeNine Five.B1positive = refl
phaseAfterModeNine Five.B2negative = refl
phaseAfterModeNine Five.B2positive = refl
phaseAfterModeNine Five.Enegative = refl
phaseAfterModeNine Five.Epositive = refl

canonicalPhaseNineToModeNineRecognition :
  PhaseNineToModeNineRecognition
canonicalPhaseNineToModeNineRecognition =
  phase-nine-to-mode-nine-recognition
    phaseNineToModeNine
    modeNineToPhaseNine
    modeAfterPhaseNine
    phaseAfterModeNine

observeABCanonicalModeNine :
  Descent.ABSection ->
  Five.ModePhaseQuotient9
observeABCanonicalModeNine =
  observeABModeNine canonicalPhaseNineToModeNineRecognition

------------------------------------------------------------------------
-- 6c. Repo-native C2 sign transport and exact observer intertwining.
--
-- This is a finite signed-trit transport.  It is NOT promoted to the analytic
-- Fricke involution or to a Monster normalizer action.
------------------------------------------------------------------------

negateSSP : SSP.SSPTrit -> SSP.SSPTrit
negateSSP SSP.sspNegOne = SSP.sspPosOne
negateSSP SSP.sspZero = SSP.sspZero
negateSSP SSP.sspPosOne = SSP.sspNegOne

negateSSPInvolutive :
  (trit : SSP.SSPTrit) ->
  negateSSP (negateSSP trit) ≡ trit
negateSSPInvolutive SSP.sspNegOne = refl
negateSSPInvolutive SSP.sspZero = refl
negateSSPInvolutive SSP.sspPosOne = refl

negateABLocal :
  Descent.ABSection ->
  Descent.ABSection
negateABLocal
  (Descent.ab-section aa ab ba bb) =
  Descent.ab-section
    (negateSSP aa)
    (negateSSP ab)
    (negateSSP ba)
    (negateSSP bb)

negateABLocalInvolutive :
  (section : Descent.ABSection) ->
  negateABLocal (negateABLocal section) ≡ section
negateABLocalInvolutive
  (Descent.ab-section aa ab ba bb)
  rewrite negateSSPInvolutive aa
        | negateSSPInvolutive ab
        | negateSSPInvolutive ba
        | negateSSPInvolutive bb = refl

negateTri : Base.TriTruth -> Base.TriTruth
negateTri Base.tri-low = Base.tri-high
negateTri Base.tri-mid = Base.tri-mid
negateTri Base.tri-high = Base.tri-low

negatePhaseNine :
  Phase.PhaseQuotient9 ->
  Phase.PhaseQuotient9
negatePhaseNine (left , right) =
  negateTri left , negateTri right

negateModeNine :
  Five.ModePhaseQuotient9 ->
  Five.ModePhaseQuotient9
negateModeNine mode =
  phaseNineToModeNine
    (negatePhaseNine (modeNineToPhaseNine mode))

negateModeNineInvolutive :
  (mode : Five.ModePhaseQuotient9) ->
  negateModeNine (negateModeNine mode) ≡ mode
negateModeNineInvolutive Five.identityMode = refl
negateModeNineInvolutive Five.A2negative = refl
negateModeNineInvolutive Five.A2positive = refl
negateModeNineInvolutive Five.B1negative = refl
negateModeNineInvolutive Five.B1positive = refl
negateModeNineInvolutive Five.B2negative = refl
negateModeNineInvolutive Five.B2positive = refl
negateModeNineInvolutive Five.Enegative = refl
negateModeNineInvolutive Five.Epositive = refl

phaseObserverIntertwinesNegation :
  (section : Descent.ABSection) ->
  observeABPhaseQuotient9 (negateABLocal section)
  ≡ negatePhaseNine (observeABPhaseQuotient9 section)
phaseObserverIntertwinesNegation
  (Descent.ab-section aa ab ba bb) = refl

modeObserverIntertwinesNegation :
  (section : Descent.ABSection) ->
  observeABCanonicalModeNine (negateABLocal section)
  ≡ negateModeNine (observeABCanonicalModeNine section)
modeObserverIntertwinesNegation
  (Descent.ab-section aa ab ba bb) = refl

data RepoNativeNegationEqualsAnalyticFricke : Set where

repoNativeNegationNotPromotedToAnalyticFricke :
  RepoNativeNegationEqualsAnalyticFricke -> ⊥
repoNativeNegationNotPromotedToAnalyticFricke ()

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
    participantC3ObserverCovariancePaid : Bool
    phaseNineToModeNineRecognitionConstructed : Bool
    phaseNineToModeNineCarrierRoundTripsPaid : Bool
    repoNativeC2TransportOwned : Bool
    candidateObserverTransportIntertwinerPaid : Bool
    repoNativeC2IdentifiedWithAnalyticFricke : Bool
    actualMonsterFiveLocalCarrierIdentified : Bool
    actualMonsterTransportIntertwinerProved : Bool

canonicalTrialectic369DyadicLocalNineObserverCandidateBoundary :
  Trialectic369DyadicLocalNineObserverCandidateBoundary
canonicalTrialectic369DyadicLocalNineObserverCandidateBoundary =
  trialectic-369-dyadic-local-nine-observer-candidate-boundary
    true true true true true true true
    true true false
    false false
