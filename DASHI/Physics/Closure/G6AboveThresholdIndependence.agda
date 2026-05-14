module DASHI.Physics.Closure.G6AboveThresholdIndependence where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.String using (String)
open import Data.Nat.Base using (_<_)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Physics.Closure.G6CrossLaneCommutingTheorem as G6
open import DASHI.Physics.Closure.G6CrossLaneCommutingTheorem using (Lane)

------------------------------------------------------------------------
-- G6 above-threshold independence surface.
--
-- The repository currently exposes the carrier primes as the finite SSP
-- enumeration ending at p71, but does not expose a Nat-prime lookup or an
-- out-of-range valuation theorem for arbitrary p > 71.  This module keeps
-- the result conditional and names the exact primitive needed to close it.

record G6AboveThresholdCarrier : Set₁ where
  field
    Carrier :
      Set

    valuationAt :
      Nat →
      Carrier →
      Nat

    laneOperator :
      Lane →
      Carrier →
      Carrier

record G6AboveThresholdPrimitiveProvider
  (surface : G6AboveThresholdCarrier) : Set₁ where
  open G6AboveThresholdCarrier surface

  field
    carrierPrimeBoundedness :
      (p : Nat) →
      (c : Carrier) →
      71 < p →
      valuationAt p c ≡ zero

    laneOperatorIdentityWhenVanishes :
      (p : Nat) →
      (lane : Lane) →
      (c : Carrier) →
      valuationAt p c ≡ zero →
      laneOperator lane c ≡ c

g6SharedCarrierPrimitiveCarrierPrimeBoundedness :
  (prim : G6.G6SharedCarrierFactorizationPrimitive) →
  (p : Nat) →
  (c : G6.G6SharedCarrierFactorizationPrimitive.SharedCarrier prim) →
  71 < p →
  G6.G6SharedCarrierFactorizationPrimitive.valuationAt prim p c
  ≡
  zero
g6SharedCarrierPrimitiveCarrierPrimeBoundedness =
  G6.carrierPrimeBoundednessFromSharedCarrierFactorizationPrimitive

G6AboveThresholdComponentEquality :
  (surface : G6AboveThresholdCarrier) →
  Set
G6AboveThresholdComponentEquality surface =
  (p : Nat) →
  (leftLane rightLane : Lane) →
  (c : G6AboveThresholdCarrier.Carrier surface) →
  71 < p →
  G6AboveThresholdCarrier.laneOperator surface leftLane c
    ≡
  G6AboveThresholdCarrier.laneOperator surface rightLane c

aboveThresholdComponentEquality :
  (surface : G6AboveThresholdCarrier) →
  G6AboveThresholdPrimitiveProvider surface →
  G6AboveThresholdComponentEquality surface
aboveThresholdComponentEquality surface provider p leftLane rightLane c p>71 =
  trans
    (G6AboveThresholdPrimitiveProvider.laneOperatorIdentityWhenVanishes
      provider p leftLane c
      (G6AboveThresholdPrimitiveProvider.carrierPrimeBoundedness
        provider p c p>71))
    (sym
      (G6AboveThresholdPrimitiveProvider.laneOperatorIdentityWhenVanishes
        provider p rightLane c
        (G6AboveThresholdPrimitiveProvider.carrierPrimeBoundedness
          provider p c p>71)))

G6AboveThresholdIndependence :
  (surface : G6AboveThresholdCarrier) →
  Set
G6AboveThresholdIndependence =
  G6AboveThresholdComponentEquality

aboveThresholdIndependence :
  (surface : G6AboveThresholdCarrier) →
  G6AboveThresholdPrimitiveProvider surface →
  G6AboveThresholdIndependence surface
aboveThresholdIndependence =
  aboveThresholdComponentEquality

g6AboveThresholdCarrierFromLaneOperator :
  G6.LaneOperator →
  G6AboveThresholdCarrier
g6AboveThresholdCarrierFromLaneOperator operator =
  record
    { Carrier =
        G6.LaneOperator.opSharedCarrier operator
    ; valuationAt =
        G6.LaneOperator.opValuationAt operator
    ; laneOperator =
        G6.LaneOperator.opSharedLaneAction operator
    }

g6AboveThresholdPrimitiveProviderFromLaneOperator :
  (operator : G6.LaneOperator) →
  G6AboveThresholdPrimitiveProvider
    (g6AboveThresholdCarrierFromLaneOperator operator)
g6AboveThresholdPrimitiveProviderFromLaneOperator operator =
  record
    { carrierPrimeBoundedness =
        G6.carrierPrimeBoundednessFromLaneOperator operator
    ; laneOperatorIdentityWhenVanishes =
        G6.LaneOperator.opSharedLaneActionIdentityWhenVanishes operator
    }

aboveThresholdIndependenceFromLaneOperator :
  (operator : G6.LaneOperator) →
  G6AboveThresholdIndependence
    (g6AboveThresholdCarrierFromLaneOperator operator)
aboveThresholdIndependenceFromLaneOperator operator =
  aboveThresholdIndependence
    (g6AboveThresholdCarrierFromLaneOperator operator)
    (g6AboveThresholdPrimitiveProviderFromLaneOperator operator)

data G6AboveThresholdStatus : Set where
  conditionalOnCarrierPrimeBoundedness :
    G6AboveThresholdStatus

  dischargedByLaneOperatorCarrierAPI :
    G6AboveThresholdStatus

record G6AboveThresholdMissingPrimitiveReport : Set where
  field
    status :
      G6AboveThresholdStatus

    missingPrimitives :
      List String

    availableCarrierSurface :
      List String

    exactSharedCarrierBlocker :
      List String

    noPromotionBoundary :
      List String

canonicalG6AboveThresholdMissingPrimitiveReport :
  G6AboveThresholdMissingPrimitiveReport
canonicalG6AboveThresholdMissingPrimitiveReport =
  record
    { status =
        dischargedByLaneOperatorCarrierAPI
    ; missingPrimitives =
        "No missing above-threshold primitive remains once an inhabited LaneOperator is supplied"
        ∷ "carrierPrimeBoundedness is provided by G6.carrierPrimeBoundednessFromLaneOperator"
        ∷ "laneOperatorIdentityWhenVanishes is provided by LaneOperator.opSharedLaneActionIdentityWhenVanishes"
        ∷ []
    ; availableCarrierSurface =
        "MonsterOntos.SSP enumerates exactly p2,p3,p5,p7,p11,p13,p17,p19,p23,p29,p31,p41,p47,p59,p71"
        ∷ "DASHI.TrackedPrimes exposes trackedPrimeList and trackedPrimeVec15 for the same 15-prime carrier"
        ∷ "Ontology.GodelLattice.FactorVec is Vec15 Nat, with no arbitrary Nat-prime out-of-range lookup exposed here"
        ∷ "G6SharedCarrierFactorizationPrimitive exports carrierPrimeBoundedness from valuationOutsideTrackedBasisVanishes only after a real shared carrier primitive is supplied"
        ∷ []
    ; exactSharedCarrierBlocker =
        "LaneOperator now exposes opSharedCarrier, opFactorVec, opValuationAt, opLaneToShared, and shared action laws"
        ∷ "aboveThresholdIndependenceFromLaneOperator derives the component equality over the LaneOperator shared carrier"
        ∷ "This module still does not construct a concrete LaneOperator inhabitant"
        ∷ []
    ; noPromotionBoundary =
        "This module does not postulate carrierPrimeBoundedness"
        ∷ "This module promotes only the above-threshold component equality conditional on an inhabited LaneOperator"
        ∷ "Full G6 promotion remains blocked by the separate CRT phase computation and carrier-filtration induction requests"
        ∷ []
    }

canonicalG6AboveThresholdStatus :
  G6AboveThresholdStatus
canonicalG6AboveThresholdStatus =
  G6AboveThresholdMissingPrimitiveReport.status
    canonicalG6AboveThresholdMissingPrimitiveReport

canonicalG6AboveThresholdStatusIsDischarged :
  canonicalG6AboveThresholdStatus
  ≡
  dischargedByLaneOperatorCarrierAPI
canonicalG6AboveThresholdStatusIsDischarged = refl
