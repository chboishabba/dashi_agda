module DASHI.Physics.Closure.NSPerLaneDecoupledSystemReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.NSFlowPreservationBoundReceipt as Flow

------------------------------------------------------------------------
-- Per-lane decoupled Navier-Stokes system receipt.
--
-- For each carrier prime p in {2,3,5,7}, this receipt records the lane
-- projection
--
--   Pi_p u = sum_j P_{p^j} u
--
-- and the projected decoupled approximation
--
--   partial_t(Pi_p u) + Pi_p[(u*nabla)u]
--     = nu Delta(Pi_p u) - nabla Pi_p q.
--
-- The within-lane term Pi_p[((Pi_p u)*nabla)(Pi_p u)] is recorded as
-- adjacent-only inside lane p.  Cross-lane perturbations
-- Pi_p[(Pi_q u*nabla)(Pi_r u)] with q != p or r != p are recorded as
-- summably small using the candidate flow-preservation bound.  This is a
-- lane-decoupling receipt only; it contains no Clay/global terminal
-- promotion.

data CarrierPrime : Set where
  p2 :
    CarrierPrime

  p3 :
    CarrierPrime

  p5 :
    CarrierPrime

  p7 :
    CarrierPrime

canonicalCarrierPrimes :
  List CarrierPrime
canonicalCarrierPrimes =
  p2
  ∷ p3
  ∷ p5
  ∷ p7
  ∷ []

data CarrierPowerBand : CarrierPrime → Set where
  P_p2^j :
    (j : Nat) →
    CarrierPowerBand p2

  P_p3^j :
    (j : Nat) →
    CarrierPowerBand p3

  P_p5^j :
    (j : Nat) →
    CarrierPowerBand p5

  P_p7^j :
    (j : Nat) →
    CarrierPowerBand p7

data PerLaneProjection : Set where
  Pi_p :
    CarrierPrime →
    PerLaneProjection

Pi2 :
  PerLaneProjection
Pi2 =
  Pi_p p2

Pi3 :
  PerLaneProjection
Pi3 =
  Pi_p p3

Pi5 :
  PerLaneProjection
Pi5 =
  Pi_p p5

Pi7 :
  PerLaneProjection
Pi7 =
  Pi_p p7

perLaneProjectionFormula :
  String
perLaneProjectionFormula =
  "Pi_p u = sum_j P_{p^j} u for p in {2,3,5,7}"

decoupledApproximationFormula :
  String
decoupledApproximationFormula =
  "partial_t(Pi_p u)+Pi_p[(u*nabla)u]=nu Delta(Pi_p u)-nabla Pi_p q"

withinLaneAdjacentOnlyFormula :
  String
withinLaneAdjacentOnlyFormula =
  "Pi_p[((Pi_p u)*nabla)(Pi_p u)] has adjacent-only interactions within lane p"

crossLanePerturbationFormula :
  String
crossLanePerturbationFormula =
  "Pi_p[(Pi_q u*nabla)(Pi_r u)] is summably small when q != p or r != p"

data WithinLaneTerm : CarrierPrime → Set where
  Pi_pPi_pTransport :
    (p : CarrierPrime) →
    WithinLaneTerm p

data WithinLaneInteractionStatus : Set where
  adjacentOnlyWithinLane :
    WithinLaneInteractionStatus

data CrossLanePerturbationStatus : Set where
  candidateFromFlowPreservation :
    CrossLanePerturbationStatus

canonicalCrossLanePerturbationStatus :
  CrossLanePerturbationStatus
canonicalCrossLanePerturbationStatus =
  candidateFromFlowPreservation

data DecoupledSystemStatus : Set where
  perLaneProjectionDefinedStatus :
    DecoupledSystemStatus

  projectedEquationRecordedStatus :
    DecoupledSystemStatus

  withinLaneAdjacentOnlyStatus :
    DecoupledSystemStatus

  crossLaneCandidateSmallStatus :
    DecoupledSystemStatus

  noClayGlobalTerminalPromotionStatus :
    DecoupledSystemStatus

canonicalDecoupledSystemStatus :
  List DecoupledSystemStatus
canonicalDecoupledSystemStatus =
  perLaneProjectionDefinedStatus
  ∷ projectedEquationRecordedStatus
  ∷ withinLaneAdjacentOnlyStatus
  ∷ crossLaneCandidateSmallStatus
  ∷ noClayGlobalTerminalPromotionStatus
  ∷ []

data ClayGlobalTerminalPromotion : Set where

clayGlobalTerminalPromotionImpossibleHere :
  ClayGlobalTerminalPromotion →
  ⊥
clayGlobalTerminalPromotionImpossibleHere ()

record NSPerLaneDecoupledSystemReceipt : Setω where
  field
    carrierPrimes :
      List CarrierPrime

    carrierPrimesAreCanonical :
      carrierPrimes ≡ canonicalCarrierPrimes

    perLaneProjectionDefined :
      CarrierPrime →
      PerLaneProjection

    perLaneProjectionDefinedIsPi_p :
      (p : CarrierPrime) →
      perLaneProjectionDefined p ≡ Pi_p p

    perLaneProjectionFormulaLabel :
      String

    perLaneProjectionFormulaLabelIsCanonical :
      perLaneProjectionFormulaLabel ≡ perLaneProjectionFormula

    decoupledApproximation :
      String

    decoupledApproximationIsCanonical :
      decoupledApproximation ≡ decoupledApproximationFormula

    withinLaneTerm :
      (p : CarrierPrime) →
      WithinLaneTerm p

    withinLaneTermIsCanonical :
      (p : CarrierPrime) →
      withinLaneTerm p ≡ Pi_pPi_pTransport p

    withinLaneTermAdjacentOnly :
      Bool

    withinLaneTermAdjacentOnlyIsTrue :
      withinLaneTermAdjacentOnly ≡ true

    withinLaneInteractionStatus :
      WithinLaneInteractionStatus

    withinLaneInteractionStatusIsAdjacentOnly :
      withinLaneInteractionStatus ≡ adjacentOnlyWithinLane

    withinLaneAdjacentOnlyLabel :
      String

    withinLaneAdjacentOnlyLabelIsCanonical :
      withinLaneAdjacentOnlyLabel ≡ withinLaneAdjacentOnlyFormula

    crossLanePerturbationFormulaLabel :
      String

    crossLanePerturbationFormulaLabelIsCanonical :
      crossLanePerturbationFormulaLabel ≡ crossLanePerturbationFormula

    crossLaneTermSummablySmall :
      CrossLanePerturbationStatus

    crossLaneTermSummablySmallIsCandidateFromFlowPreservation :
      crossLaneTermSummablySmall ≡ canonicalCrossLanePerturbationStatus

    flowPreservationCandidateSource :
      Flow.NSFlowPreservationBoundReceipt

    decoupledApproximationWellDefined :
      Bool

    decoupledApproximationWellDefinedIsTrue :
      decoupledApproximationWellDefined ≡ true

    status :
      List DecoupledSystemStatus

    statusIsCanonical :
      status ≡ canonicalDecoupledSystemStatus

    clayGlobalTerminalPromoted :
      Bool

    clayGlobalTerminalPromotedIsFalse :
      clayGlobalTerminalPromoted ≡ false

    clayGlobalTerminalPromotionFlags :
      List ClayGlobalTerminalPromotion

    clayGlobalTerminalPromotionFlagsAreEmpty :
      clayGlobalTerminalPromotionFlags ≡ []

    receiptBoundary :
      List String

open NSPerLaneDecoupledSystemReceipt public

canonicalNSPerLaneDecoupledSystemReceipt :
  NSPerLaneDecoupledSystemReceipt
canonicalNSPerLaneDecoupledSystemReceipt =
  record
    { carrierPrimes =
        canonicalCarrierPrimes
    ; carrierPrimesAreCanonical =
        refl
    ; perLaneProjectionDefined =
        Pi_p
    ; perLaneProjectionDefinedIsPi_p =
        λ _ → refl
    ; perLaneProjectionFormulaLabel =
        perLaneProjectionFormula
    ; perLaneProjectionFormulaLabelIsCanonical =
        refl
    ; decoupledApproximation =
        decoupledApproximationFormula
    ; decoupledApproximationIsCanonical =
        refl
    ; withinLaneTerm =
        Pi_pPi_pTransport
    ; withinLaneTermIsCanonical =
        λ _ → refl
    ; withinLaneTermAdjacentOnly =
        true
    ; withinLaneTermAdjacentOnlyIsTrue =
        refl
    ; withinLaneInteractionStatus =
        adjacentOnlyWithinLane
    ; withinLaneInteractionStatusIsAdjacentOnly =
        refl
    ; withinLaneAdjacentOnlyLabel =
        withinLaneAdjacentOnlyFormula
    ; withinLaneAdjacentOnlyLabelIsCanonical =
        refl
    ; crossLanePerturbationFormulaLabel =
        crossLanePerturbationFormula
    ; crossLanePerturbationFormulaLabelIsCanonical =
        refl
    ; crossLaneTermSummablySmall =
        canonicalCrossLanePerturbationStatus
    ; crossLaneTermSummablySmallIsCandidateFromFlowPreservation =
        refl
    ; flowPreservationCandidateSource =
        Flow.canonicalNSFlowPreservationBoundReceipt
    ; decoupledApproximationWellDefined =
        true
    ; decoupledApproximationWellDefinedIsTrue =
        refl
    ; status =
        canonicalDecoupledSystemStatus
    ; statusIsCanonical =
        refl
    ; clayGlobalTerminalPromoted =
        false
    ; clayGlobalTerminalPromotedIsFalse =
        refl
    ; clayGlobalTerminalPromotionFlags =
        []
    ; clayGlobalTerminalPromotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "Per-lane projections Pi_p u = sum_j P_{p^j} u are recorded for p=2,3,5,7"
        ∷ "The projected decoupled approximation is recorded lane-by-lane"
        ∷ "Within-lane transport is recorded as adjacent-only within the same carrier prime lane"
        ∷ "Cross-lane perturbations are summably small only as candidateFromFlowPreservation"
        ∷ "No Clay/global terminal promotion is introduced by this receipt"
        ∷ []
    }

perLaneProjectionDefinedPi_p :
  (p : CarrierPrime) →
  perLaneProjectionDefined canonicalNSPerLaneDecoupledSystemReceipt p
  ≡
  Pi_p p
perLaneProjectionDefinedPi_p _ =
  refl

withinLaneTermAdjacentOnlyTrue :
  withinLaneTermAdjacentOnly canonicalNSPerLaneDecoupledSystemReceipt
  ≡
  true
withinLaneTermAdjacentOnlyTrue =
  refl

crossLaneTermSummablySmallCandidateFromFlowPreservation :
  crossLaneTermSummablySmall canonicalNSPerLaneDecoupledSystemReceipt
  ≡
  candidateFromFlowPreservation
crossLaneTermSummablySmallCandidateFromFlowPreservation =
  refl

decoupledApproximationWellDefinedTrue :
  decoupledApproximationWellDefined canonicalNSPerLaneDecoupledSystemReceipt
  ≡
  true
decoupledApproximationWellDefinedTrue =
  refl

clayGlobalTerminalPromotedFalse :
  clayGlobalTerminalPromoted canonicalNSPerLaneDecoupledSystemReceipt
  ≡
  false
clayGlobalTerminalPromotedFalse =
  refl
