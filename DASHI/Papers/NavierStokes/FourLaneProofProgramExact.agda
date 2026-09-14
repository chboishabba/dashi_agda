module DASHI.Papers.NavierStokes.FourLaneProofProgramExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- NAVIER-STOKES A/B/C/D PROOF-PROGRAM FIREWALL
--
-- Timestamp: 2026-09-15 09:32 AEST (UTC+10).
--
-- This owner is programme/provenance structure, not a PDE theorem.  It freezes
-- the nomenclature used by the live manuscript and proof-control records:
--
--   A = unforced whole-space R^3 regularity
--   B = unforced periodic T^3 regularity
--   C = forced whole-space R^3 breakdown
--   D = forced periodic T^3 breakdown
--
-- The B R571 -> centered/Taylor -> six-three -> R568 construction must not be
-- silently promoted into A.  Conversely, A progress does not automatically
-- descend to B.  C/D released-proof verification/provenance does not settle
-- either unforced alternative.
------------------------------------------------------------------------

data NSClayLane : Set where
  wholeSpaceA periodicB forcedWholeSpaceC forcedPeriodicD : NSClayLane

record NSFourLaneProofProgram : Set where
  constructor ns-four-lane-proof-program
  field
    laneA laneB laneC laneD : NSClayLane

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
-- Canonical lane identities.
------------------------------------------------------------------------

laneAIsWholeSpace : laneA canonicalNSFourLaneProofProgram ≡ wholeSpaceA
laneAIsWholeSpace = refl

laneBIsPeriodic : laneB canonicalNSFourLaneProofProgram ≡ periodicB
laneBIsPeriodic = refl

laneCIsForcedWholeSpace : laneC canonicalNSFourLaneProofProgram ≡ forcedWholeSpaceC
laneCIsForcedWholeSpace = refl

laneDIsForcedPeriodic : laneD canonicalNSFourLaneProofProgram ≡ forcedPeriodicD
laneDIsForcedPeriodic = refl

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
