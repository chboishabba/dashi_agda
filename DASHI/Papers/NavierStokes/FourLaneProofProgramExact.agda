module DASHI.Papers.NavierStokes.FourLaneProofProgramExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.NSClayFourAlternativeReleasedProofBidiExact as Four

------------------------------------------------------------------------
-- NAVIER-STOKES A/B/C/D PAPER/PROGRAMME ADAPTER
--
-- Timestamp: 2026-09-15 09:32 AEST (UTC+10).
--
-- This file deliberately DOES NOT introduce a second four-alternative
-- ontology.  The canonical mathematical/source alternatives already live in
-- NSClayFourAlternativeReleasedProofBidiExact.  This owner only adds the
-- current Paper-1 route selection, historical/provenance status, and explicit
-- A<->B transfer guards on top of that existing typed source surface.
------------------------------------------------------------------------

NSClayLane : Set
NSClayLane = Four.ClayAlternative4

wholeSpaceA : NSClayLane
wholeSpaceA = Four.A-euclidean-unforced-global

periodicB : NSClayLane
periodicB = Four.B-periodic-unforced-global

forcedWholeSpaceC : NSClayLane
forcedWholeSpaceC = Four.C-euclidean-forced-breakdown

forcedPeriodicD : NSClayLane
forcedPeriodicD = Four.D-periodic-forced-breakdown

record NSFourLaneProofProgram : Set where
  constructor ns-four-lane-proof-program
  field
    laneA laneB laneC laneD : NSClayLane

    statusA statusB statusC statusD : Four.AlternativeStatusReceipt4

    laneADescription : String
    laneBDescription : String
    laneCDescription : String
    laneDDescription : String

    periodicBIsActiveConstruction : Bool
    wholeSpaceAIsIndependentObligation : Bool
    forcedCDIsVerificationAndProvenance : Bool

    r571CenteredTaylorSixThreeR568IsPeriodicB : Bool
    periodicBR571TaylorRealizationClosed : Bool
    periodicBSecondMomentSixThreeTransplantClosed : Bool
    periodicBR568PaymentClosed : Bool

    wholeSpaceACurrentTerminalCutFrozen : Bool

    periodicBToWholeSpaceATransferConstructed : Bool
    wholeSpaceAToPeriodicBTransferConstructed : Bool
    periodicBProofProgressDoesNotPromoteWholeSpaceA : Bool
    wholeSpaceAProofProgressDoesNotPromotePeriodicB : Bool
    forcedCDDoesNotSettleUnforcedAB : Bool

    gramP3AttemptRetainedAsHistoricalProvenance : Bool
    gramP3AttemptAbandonedAsPrimaryRoute : Bool
    gramP3AbandonmentReason : String

open NSFourLaneProofProgram public

canonicalNSFourLaneProofProgram : NSFourLaneProofProgram
canonicalNSFourLaneProofProgram =
  ns-four-lane-proof-program
    wholeSpaceA
    periodicB
    forcedWholeSpaceC
    forcedPeriodicD
    Four.statusA4
    Four.statusB4
    Four.statusC4
    Four.statusD4
    "Lane A: unforced three-dimensional Navier-Stokes regularity on whole-space R^3. Independent proof obligation unless an explicit transfer theorem is constructed."
    "Lane B: unforced three-dimensional periodic Navier-Stokes regularity on T^3. Active construction lane: R571 signed helical carrier -> centered/Taylor realization -> second moment -> six-three -> signed inner-fibre payment -> R568."
    "Lane C: forced whole-space R^3 breakdown. Current job is released-proof BIDI verification, provenance, dependency closure, and same-object integration; it is not discovery evidence for A or B."
    "Lane D: forced periodic T^3 breakdown. Current job is released-proof BIDI verification, provenance, dependency closure, and same-object integration; it is not discovery evidence for A or B."
    true
    true
    true
    true
    false
    false
    false
    false
    false
    false
    true
    true
    true
    true
    true
    "The partner-first/same-output Gram route, PSD compressed-difference carrier, complete-graph/P3 separation attempt, and R214 constant-band no-go are retained append-only. The route was abandoned as the primary producer after the exact amplitude telescope exposed a many-to-one observable map: incidence geometry alone cannot force separation when distinct same-output incidences can carry equal velocity arguments and therefore equal compressed slot kernels. This is a route-selection result, not a deletion or refutation of the theorem-bearing Gram infrastructure."

------------------------------------------------------------------------
-- Canonical lane/source identity is inherited from the existing Four owner.
------------------------------------------------------------------------

laneAIsWholeSpace : laneA canonicalNSFourLaneProofProgram ≡ Four.A-euclidean-unforced-global
laneAIsWholeSpace = refl

laneBIsPeriodic : laneB canonicalNSFourLaneProofProgram ≡ Four.B-periodic-unforced-global
laneBIsPeriodic = refl

laneCIsForcedWholeSpace : laneC canonicalNSFourLaneProofProgram ≡ Four.C-euclidean-forced-breakdown
laneCIsForcedWholeSpace = refl

laneDIsForcedPeriodic : laneD canonicalNSFourLaneProofProgram ≡ Four.D-periodic-forced-breakdown
laneDIsForcedPeriodic = refl

statusAIsCanonical : statusA canonicalNSFourLaneProofProgram ≡ Four.statusA4
statusAIsCanonical = refl

statusBIsCanonical : statusB canonicalNSFourLaneProofProgram ≡ Four.statusB4
statusBIsCanonical = refl

statusCIsCanonical : statusC canonicalNSFourLaneProofProgram ≡ Four.statusC4
statusCIsCanonical = refl

statusDIsCanonical : statusD canonicalNSFourLaneProofProgram ≡ Four.statusD4
statusDIsCanonical = refl

-- Re-export the stronger existing typed firewall: a forced-breakdown witness
-- cannot be reused as permission to pay an unforced alternative.
forcedBreakdownDoesNotPayUnforcedAlternative :
  Four.ForcedBreakdownPaysUnforcedAlternativePermission4 → ⊥
forcedBreakdownDoesNotPayUnforcedAlternative =
  Four.forcedBreakdownDoesNotPayUnforcedAlternative4

------------------------------------------------------------------------
-- Fail-closed route and transfer status.
------------------------------------------------------------------------

periodicBIsActiveConstructionIsTrue :
  periodicBIsActiveConstruction canonicalNSFourLaneProofProgram ≡ true
periodicBIsActiveConstructionIsTrue = refl

wholeSpaceAIsIndependentObligationIsTrue :
  wholeSpaceAIsIndependentObligation canonicalNSFourLaneProofProgram ≡ true
wholeSpaceAIsIndependentObligationIsTrue = refl

forcedCDIsVerificationAndProvenanceIsTrue :
  forcedCDIsVerificationAndProvenance canonicalNSFourLaneProofProgram ≡ true
forcedCDIsVerificationAndProvenanceIsTrue = refl

periodicBToWholeSpaceATransferConstructedIsFalse :
  periodicBToWholeSpaceATransferConstructed canonicalNSFourLaneProofProgram ≡ false
periodicBToWholeSpaceATransferConstructedIsFalse = refl

wholeSpaceAToPeriodicBTransferConstructedIsFalse :
  wholeSpaceAToPeriodicBTransferConstructed canonicalNSFourLaneProofProgram ≡ false
wholeSpaceAToPeriodicBTransferConstructedIsFalse = refl

periodicBProofProgressDoesNotPromoteWholeSpaceAIsTrue :
  periodicBProofProgressDoesNotPromoteWholeSpaceA canonicalNSFourLaneProofProgram ≡ true
periodicBProofProgressDoesNotPromoteWholeSpaceAIsTrue = refl

wholeSpaceAProofProgressDoesNotPromotePeriodicBIsTrue :
  wholeSpaceAProofProgressDoesNotPromotePeriodicB canonicalNSFourLaneProofProgram ≡ true
wholeSpaceAProofProgressDoesNotPromotePeriodicBIsTrue = refl

forcedCDDoesNotSettleUnforcedABIsTrue :
  forcedCDDoesNotSettleUnforcedAB canonicalNSFourLaneProofProgram ≡ true
forcedCDDoesNotSettleUnforcedABIsTrue = refl

------------------------------------------------------------------------
-- Historical route retention.
------------------------------------------------------------------------

gramP3AttemptRetainedAsHistoricalProvenanceIsTrue :
  gramP3AttemptRetainedAsHistoricalProvenance canonicalNSFourLaneProofProgram ≡ true
gramP3AttemptRetainedAsHistoricalProvenanceIsTrue = refl

gramP3AttemptAbandonedAsPrimaryRouteIsTrue :
  gramP3AttemptAbandonedAsPrimaryRoute canonicalNSFourLaneProofProgram ≡ true
gramP3AttemptAbandonedAsPrimaryRouteIsTrue = refl

------------------------------------------------------------------------
-- Active B proof frontier remains open.
------------------------------------------------------------------------

periodicBR571TaylorRealizationClosedIsFalse :
  periodicBR571TaylorRealizationClosed canonicalNSFourLaneProofProgram ≡ false
periodicBR571TaylorRealizationClosedIsFalse = refl

periodicBSecondMomentSixThreeTransplantClosedIsFalse :
  periodicBSecondMomentSixThreeTransplantClosed canonicalNSFourLaneProofProgram ≡ false
periodicBSecondMomentSixThreeTransplantClosedIsFalse = refl

periodicBR568PaymentClosedIsFalse :
  periodicBR568PaymentClosed canonicalNSFourLaneProofProgram ≡ false
periodicBR568PaymentClosedIsFalse = refl

wholeSpaceACurrentTerminalCutFrozenIsFalse :
  wholeSpaceACurrentTerminalCutFrozen canonicalNSFourLaneProofProgram ≡ false
wholeSpaceACurrentTerminalCutFrozenIsFalse = refl
