module DASHI.Physics.Plasma.MHDEnergyCrossHelicityTriadBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Plasma.MHDElsasserTangentRechartExact as ET

------------------------------------------------------------------------
-- ENERGY / CROSS-HELICITY TRIAD BIDI CONSUMER
--
-- The exact coordinate algebra reduces total-energy and cross-helicity tests to
-- the plus/minus Elsasser quadratic-energy variations.  But an individual
-- p,q->k tangent is not the whole conservative triad: a literal cyclic receipt
-- over the k,p,q output slots is still required.
------------------------------------------------------------------------

record ElsasserQuadraticVariation {r : _} (F : C3.RealField r) : Set r where
  constructor elsasser-quadratic-variation
  field
    plusVariation : C3.Carrier F
    minusVariation : C3.Carrier F
    sameObjectElsasserTangentReceipt : Set
    literalQuadraticObserverReceipt : Set

open ElsasserQuadraticVariation public

record CyclicTriadElsasserBalance {r : _} (F : C3.RealField r) : Set r where
  constructor cyclic-triad-elsasser-balance
  field
    kSlot pSlot qSlot : ElsasserQuadraticVariation F
    plusCyclicCancellation : Set
    minusCyclicCancellation : Set
    sameLiteralTriadAcrossSlots : Set
    pressureProjectionCancellation : Set
    balanceReference : String

open CyclicTriadElsasserBalance public

record EnergyCrossHelicityCancellationReceipt {r : _} (F : C3.RealField r) : Set r where
  constructor energy-cross-helicity-cancellation-receipt
  field
    cyclicBalance : CyclicTriadElsasserBalance F
    totalEnergyVariationCancels : Set
    crossHelicityVariationCancels : Set
    coordinateAlgebraSameObjectReceipt : Set
    cancellationReference : String

open EnergyCrossHelicityCancellationReceipt public

record EnergyCrossHelicityBidiBoundary : Set where
  constructor energy-cross-helicity-bidi-boundary
  field
    oneOutputTangentProvesTriadEnergyConservation : Bool
    oneOutputTangentProvesTriadEnergyConservationIsFalse :
      oneOutputTangentProvesTriadEnergyConservation ≡ false

    plusCyclicCancellationAloneProvesCrossHelicity : Bool
    plusCyclicCancellationAloneProvesCrossHelicityIsFalse :
      plusCyclicCancellationAloneProvesCrossHelicity ≡ false

    plusAndMinusCyclicBalancesAreSufficientConsumerInputs : Bool
    plusAndMinusCyclicBalancesAreSufficientConsumerInputsIsTrue :
      plusAndMinusCyclicBalancesAreSufficientConsumerInputs ≡ true

    pressureProjectionReceiptStillRequired : Bool
    pressureProjectionReceiptStillRequiredIsTrue :
      pressureProjectionReceiptStillRequired ≡ true

canonicalEnergyCrossHelicityBidiBoundary : EnergyCrossHelicityBidiBoundary
canonicalEnergyCrossHelicityBidiBoundary =
  energy-cross-helicity-bidi-boundary false refl false refl true refl true refl
