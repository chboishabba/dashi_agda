module DASHI.Physics.Plasma.MHDIdealInvariantTriadTestBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Plasma.MHDHelicalElsasserTriadTangentExact as Tangent

------------------------------------------------------------------------
-- IDEAL-INVARIANT TRIAD TEST SOCKET
--
-- The paired tangent is the producer.  Conservation of total energy, cross
-- helicity, or magnetic helicity is a separate consumer test.  No invariant is
-- promoted merely because the mixed Elsasser support is correct.
------------------------------------------------------------------------

data IdealInvariantKind : Set where
  totalEnergyInvariant
  crossHelicityInvariant
  magneticHelicityInvariant
  : IdealInvariantKind

record TriadInvariantTest : Set₁ where
  constructor triad-invariant-test
  field
    State TangentCarrier Scalar : Set
    tangent : State → TangentCarrier
    invariantKind : IdealInvariantKind
    directionalVariation : State → TangentCarrier → Scalar
    zeroScalar : Scalar
    testReference : String

open TriadInvariantTest public

record TriadInvariantCancellationReceipt
    (test : TriadInvariantTest) : Set₁ where
  constructor triad-invariant-cancellation-receipt
  field
    state : State test
    sameObjectPairedTangentReceipt : Set
    literalInvariantObserverReceipt : Set
    variationCancels :
      directionalVariation test state (tangent test state) ≡ zeroScalar test
    cancellationReference : String

open TriadInvariantCancellationReceipt public

record IdealInvariantTriadBidiBoundary : Set where
  constructor ideal-invariant-triad-bidi-boundary
  field
    mixedElsasserSupportAloneProvesEnergyConservation : Bool
    mixedElsasserSupportAloneProvesEnergyConservationIsFalse :
      mixedElsasserSupportAloneProvesEnergyConservation ≡ false

    momentumZeroSumAloneProvesCrossHelicityConservation : Bool
    momentumZeroSumAloneProvesCrossHelicityConservationIsFalse :
      momentumZeroSumAloneProvesCrossHelicityConservation ≡ false

    oneInvariantCancellationProvesAllIdealInvariants : Bool
    oneInvariantCancellationProvesAllIdealInvariantsIsFalse :
      oneInvariantCancellationProvesAllIdealInvariants ≡ false

    eachInvariantRequiresSameObjectDirectionalVariation : Bool
    eachInvariantRequiresSameObjectDirectionalVariationIsTrue :
      eachInvariantRequiresSameObjectDirectionalVariation ≡ true

canonicalIdealInvariantTriadBidiBoundary : IdealInvariantTriadBidiBoundary
canonicalIdealInvariantTriadBidiBoundary =
  ideal-invariant-triad-bidi-boundary false refl false refl false refl true refl
