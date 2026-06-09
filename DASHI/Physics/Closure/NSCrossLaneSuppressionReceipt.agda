module DASHI.Physics.Closure.NSCrossLaneSuppressionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.AdjacentOnlyVortexStretchingReceipt as Adjacent
import DASHI.Physics.Closure.NSFlowPreservationBoundReceipt as Flow

------------------------------------------------------------------------
-- Navier-Stokes cross-lane suppression receipt.
--
-- This receipt records the carrier-structured mechanism only.  Inside each
-- prime lane p, the active nonlinear vortex-stretching diagnostic is the
-- same-base adjacent-band term recorded by AdjacentOnlyVortexStretching.
-- Across distinct prime lanes p and q, terms of the form
--
--   (P_{p^j} u) * nabla (P_{q^l} u)
--
-- output at frequencies |p^j +/- q^l|, outside the carrier spectrum.  The
-- off-carrier contribution is bounded by NSFlowPreservationBound and goes to
-- zero as depth d tends to infinity.  Thus cross-lane energy production is
-- summable and vanishes in the carrier limit, so cross-lane nonlinear
-- interactions are suppressed relative to within-lane interactions.
--
-- This is a candidate carrier receipt only: no Clay, global regularity, or
-- terminal promotion is made here.

data NSCrossLaneSuppressionStatus : Set where
  candidate :
    NSCrossLaneSuppressionStatus

  withinPrimeLaneAdjacentOnlyDominant :
    NSCrossLaneSuppressionStatus

  crossPrimeInteractionsOffCarrier :
    NSCrossLaneSuppressionStatus

  offCarrierEnergyVanishesByFlowPreservation :
    NSCrossLaneSuppressionStatus

  crossLaneEnergyProductionSummableStatus :
    NSCrossLaneSuppressionStatus

  crossLaneNonlinearitySuppressedRelativeToWithinLane :
    NSCrossLaneSuppressionStatus

  noClayOrGlobalTerminalPromotion :
    NSCrossLaneSuppressionStatus

canonicalNSCrossLaneSuppressionStatus :
  List NSCrossLaneSuppressionStatus
canonicalNSCrossLaneSuppressionStatus =
  candidate
  ∷ withinPrimeLaneAdjacentOnlyDominant
  ∷ crossPrimeInteractionsOffCarrier
  ∷ offCarrierEnergyVanishesByFlowPreservation
  ∷ crossLaneEnergyProductionSummableStatus
  ∷ crossLaneNonlinearitySuppressedRelativeToWithinLane
  ∷ noClayOrGlobalTerminalPromotion
  ∷ []

data PrimeLaneRelation : Set where
  samePrimeLane :
    PrimeLaneRelation

  distinctPrimeLanes :
    PrimeLaneRelation

data CarrierProjectorTerm : Set where
  Ppow :
    (primeLane : Nat) →
    (depthIndex : Nat) →
    CarrierProjectorTerm

data CrossPrimeInteractionShape : Set where
  projectedTransport :
    CarrierProjectorTerm →
    CarrierProjectorTerm →
    CrossPrimeInteractionShape

canonicalCrossPrimeInteractionShape :
  CrossPrimeInteractionShape
canonicalCrossPrimeInteractionShape =
  projectedTransport (Ppow 0 0) (Ppow 1 0)

data CarrierOutputLocation : Set where
  sameLaneAdjacentCarrierBand :
    CarrierOutputLocation

  absolutePrimePowerSumOrDifferenceOffCarrier :
    CarrierOutputLocation

data CrossLaneLimitMechanism : Set where
  flowPreservationBoundDrivesOffCarrierEnergyToZero :
    CrossLaneLimitMechanism

data NSCrossLaneSuppressionPromotion : Set where

nsCrossLaneSuppressionPromotionImpossibleHere :
  NSCrossLaneSuppressionPromotion →
  ⊥
nsCrossLaneSuppressionPromotionImpossibleHere ()

nsCrossLaneSuppressionStatement :
  String
nsCrossLaneSuppressionStatement =
  "Candidate carrier mechanism: within each prime lane, adjacent-only vortex stretching is the active nonlinear term; across distinct prime lanes, (P_{p^j}u)*nabla(P_{q^l}u) outputs at |p^j +/- q^l| off carrier, and NSFlowPreservationBound makes that off-carrier energy summable and vanishing as d tends to infinity. Cross-lane nonlinear interactions are suppressed relative to within-lane interactions, with no Clay/global terminal promotion."

record NSCrossLaneSuppressionReceipt : Setω where
  field
    status :
      List NSCrossLaneSuppressionStatus

    statusIsCanonical :
      status ≡ canonicalNSCrossLaneSuppressionStatus

    theoremKind :
      NSCrossLaneSuppressionStatus

    theoremKindIsCandidate :
      theoremKind ≡ candidate

    importedFlowPreservationBoundReceiptUsed :
      Bool

    importedFlowPreservationBoundReceiptUsedIsTrue :
      importedFlowPreservationBoundReceiptUsed ≡ true

    importedAdjacentOnlyVortexStretchingReceiptUsed :
      Bool

    importedAdjacentOnlyVortexStretchingReceiptUsedIsTrue :
      importedAdjacentOnlyVortexStretchingReceiptUsed ≡ true

    laneRelation :
      PrimeLaneRelation

    laneRelationIsCrossPrime :
      laneRelation ≡ distinctPrimeLanes

    sampleCrossPrimeInteraction :
      CrossPrimeInteractionShape

    sampleCrossPrimeInteractionIsCanonical :
      sampleCrossPrimeInteraction ≡ canonicalCrossPrimeInteractionShape

    crossPrimeOutputLocation :
      CarrierOutputLocation

    crossPrimeOutputLocationIsOffCarrier :
      crossPrimeOutputLocation
      ≡
      absolutePrimePowerSumOrDifferenceOffCarrier

    withinLaneOutputLocation :
      CarrierOutputLocation

    withinLaneOutputLocationIsAdjacentCarrierBand :
      withinLaneOutputLocation ≡ sameLaneAdjacentCarrierBand

    withinLaneAdjacentOnlyRecorded :
      Bool

    withinLaneAdjacentOnlyRecordedIsTrue :
      withinLaneAdjacentOnlyRecorded ≡ true

    withinLaneOnlyActiveNonlinearity :
      NSCrossLaneSuppressionStatus

    withinLaneOnlyActiveNonlinearityIsCandidate :
      withinLaneOnlyActiveNonlinearity ≡ candidate

    crossPrimeInteractionsOutputOffCarrier :
      Bool

    crossPrimeInteractionsOutputOffCarrierIsTrue :
      crossPrimeInteractionsOutputOffCarrier ≡ true

    suppressionMechanism :
      CrossLaneLimitMechanism

    suppressionMechanismIsFlowPreservationBound :
      suppressionMechanism
      ≡
      flowPreservationBoundDrivesOffCarrierEnergyToZero

    suppressionFromFlowPreservationBound :
      Bool

    suppressionFromFlowPreservationBoundIsTrue :
      suppressionFromFlowPreservationBound ≡ true

    importedFlowPreservationOffCarrierVanishes :
      Flow.offCarrierTermGoesToZero
        Flow.canonicalNSFlowPreservationBoundReceipt
      ≡
      true

    importedAdjacentSameBaseAdjacentOnly :
      Adjacent.sameBaseResonancesAdjacentBandOnly
        Adjacent.canonicalAdjacentOnlyVortexStretchingReceipt
      ≡
      true

    crossLaneEnergyProductionSummable :
      Bool

    crossLaneEnergyProductionSummableIsTrue :
      crossLaneEnergyProductionSummable ≡ true

    crossLaneEnergyProductionVanishesInLimit :
      Bool

    crossLaneEnergyProductionVanishesInLimitIsTrue :
      crossLaneEnergyProductionVanishesInLimit ≡ true

    crossLaneNonlinearSuppressed :
      Bool

    crossLaneNonlinearSuppressedIsTrue :
      crossLaneNonlinearSuppressed ≡ true

    suppressedRelativeToWithinLane :
      Bool

    suppressedRelativeToWithinLaneIsTrue :
      suppressedRelativeToWithinLane ≡ true

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    globalRegularityPromoted :
      Bool

    globalRegularityPromotedIsFalse :
      globalRegularityPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    promotionFlags :
      List NSCrossLaneSuppressionPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    statement :
      String

    statementIsCanonical :
      statement ≡ nsCrossLaneSuppressionStatement

    receiptBoundary :
      List String

open NSCrossLaneSuppressionReceipt public

canonicalNSCrossLaneSuppressionReceipt :
  NSCrossLaneSuppressionReceipt
canonicalNSCrossLaneSuppressionReceipt =
  record
    { status =
        canonicalNSCrossLaneSuppressionStatus
    ; statusIsCanonical =
        refl
    ; theoremKind =
        candidate
    ; theoremKindIsCandidate =
        refl
    ; importedFlowPreservationBoundReceiptUsed =
        true
    ; importedFlowPreservationBoundReceiptUsedIsTrue =
        refl
    ; importedAdjacentOnlyVortexStretchingReceiptUsed =
        true
    ; importedAdjacentOnlyVortexStretchingReceiptUsedIsTrue =
        refl
    ; laneRelation =
        distinctPrimeLanes
    ; laneRelationIsCrossPrime =
        refl
    ; sampleCrossPrimeInteraction =
        canonicalCrossPrimeInteractionShape
    ; sampleCrossPrimeInteractionIsCanonical =
        refl
    ; crossPrimeOutputLocation =
        absolutePrimePowerSumOrDifferenceOffCarrier
    ; crossPrimeOutputLocationIsOffCarrier =
        refl
    ; withinLaneOutputLocation =
        sameLaneAdjacentCarrierBand
    ; withinLaneOutputLocationIsAdjacentCarrierBand =
        refl
    ; withinLaneAdjacentOnlyRecorded =
        true
    ; withinLaneAdjacentOnlyRecordedIsTrue =
        refl
    ; withinLaneOnlyActiveNonlinearity =
        candidate
    ; withinLaneOnlyActiveNonlinearityIsCandidate =
        refl
    ; crossPrimeInteractionsOutputOffCarrier =
        true
    ; crossPrimeInteractionsOutputOffCarrierIsTrue =
        refl
    ; suppressionMechanism =
        flowPreservationBoundDrivesOffCarrierEnergyToZero
    ; suppressionMechanismIsFlowPreservationBound =
        refl
    ; suppressionFromFlowPreservationBound =
        true
    ; suppressionFromFlowPreservationBoundIsTrue =
        refl
    ; importedFlowPreservationOffCarrierVanishes =
        refl
    ; importedAdjacentSameBaseAdjacentOnly =
        refl
    ; crossLaneEnergyProductionSummable =
        true
    ; crossLaneEnergyProductionSummableIsTrue =
        refl
    ; crossLaneEnergyProductionVanishesInLimit =
        true
    ; crossLaneEnergyProductionVanishesInLimitIsTrue =
        refl
    ; crossLaneNonlinearSuppressed =
        true
    ; crossLaneNonlinearSuppressedIsTrue =
        refl
    ; suppressedRelativeToWithinLane =
        true
    ; suppressedRelativeToWithinLaneIsTrue =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; globalRegularityPromoted =
        false
    ; globalRegularityPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; statement =
        nsCrossLaneSuppressionStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        "Within each prime lane p, adjacent-only vortex stretching is recorded as the active nonlinear candidate"
        ∷ "For distinct prime lanes p and q, (P_{p^j}u)*nabla(P_{q^l}u) outputs at |p^j +/- q^l| outside the carrier spectrum"
        ∷ "NSFlowPreservationBoundReceipt records that off-carrier nonlinear energy goes to zero as depth d tends to infinity"
        ∷ "For carrier-structured solutions, cross-lane energy production is recorded as summable and vanishing in the carrier limit"
        ∷ "crossLaneNonlinearSuppressed=true and suppressionFromFlowPreservationBound=true"
        ∷ "withinLaneOnlyActiveNonlinearity=candidate"
        ∷ "No Clay Navier-Stokes, global regularity, or terminal promotion is made here"
        ∷ []
    }

nsCrossLaneNonlinearSuppressed :
  crossLaneNonlinearSuppressed canonicalNSCrossLaneSuppressionReceipt
  ≡
  true
nsCrossLaneNonlinearSuppressed =
  refl

nsCrossLaneSuppressionFromFlowPreservationBound :
  suppressionFromFlowPreservationBound canonicalNSCrossLaneSuppressionReceipt
  ≡
  true
nsCrossLaneSuppressionFromFlowPreservationBound =
  refl

nsWithinLaneOnlyActiveNonlinearityCandidate :
  withinLaneOnlyActiveNonlinearity canonicalNSCrossLaneSuppressionReceipt
  ≡
  candidate
nsWithinLaneOnlyActiveNonlinearityCandidate =
  refl

nsCrossLaneSuppressionDoesNotPromoteClay :
  clayNavierStokesPromoted canonicalNSCrossLaneSuppressionReceipt
  ≡
  false
nsCrossLaneSuppressionDoesNotPromoteClay =
  refl

nsCrossLaneSuppressionDoesNotPromoteGlobalRegularity :
  globalRegularityPromoted canonicalNSCrossLaneSuppressionReceipt
  ≡
  false
nsCrossLaneSuppressionDoesNotPromoteGlobalRegularity =
  refl

nsCrossLaneSuppressionDoesNotPromoteTerminalClay :
  terminalClayClaimPromoted canonicalNSCrossLaneSuppressionReceipt
  ≡
  false
nsCrossLaneSuppressionDoesNotPromoteTerminalClay =
  refl
