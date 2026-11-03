{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkHolographicResidualTransportExact where

open import DASHI.Core.Prelude

import DASHI.Core.ConsumerKernelQuotientPresentationExact as Kernel
import DASHI.Quantum.QuantumBirthmarkErgodicityExact as Birthmark
import DASHI.Quantum.QuantumBirthmarkHolographyBridgeExact as Holography

------------------------------------------------------------------------
-- CONSUMER-RELATIVE BIRTHMARK TRANSPORT ACROSS A BOUNDARY MAP
--
-- Full bulk reconstruction is stronger than is needed to preserve one declared
-- observable.  For the birthmark consumer it is enough to pay a factorisation
--
--   bulkBirthmark = boundaryBirthmark o toBoundary.
--
-- This is the exact top-down / consumer-kernel reading already used elsewhere
-- in DASHI.  It does NOT identify the transported observable with entropy,
-- residual-information density, or a complete bulk state.
------------------------------------------------------------------------

record BirthmarkObservableTransport : Set₁ where
  field
    BulkState : Set
    BoundaryState : Set
    BirthmarkValue : Set

    toBoundary : BulkState → BoundaryState
    bulkBirthmark : BulkState → BirthmarkValue
    boundaryBirthmark : BoundaryState → BirthmarkValue

    transportLaw :
      (bulk : BulkState) →
      boundaryBirthmark (toBoundary bulk) ≡ bulkBirthmark bulk

open BirthmarkObservableTransport public

------------------------------------------------------------------------
-- Exact same-observation consequence.
------------------------------------------------------------------------

boundaryEqualityPreservesBirthmark :
  (T : BirthmarkObservableTransport) →
  (left right : BulkState T) →
  toBoundary T left ≡ toBoundary T right →
  bulkBirthmark T left ≡ bulkBirthmark T right
boundaryEqualityPreservesBirthmark T left right same =
  trans
    (sym (transportLaw T left))
    (trans
      (cong (boundaryBirthmark T) same)
      (transportLaw T right))

------------------------------------------------------------------------
-- Canonical consumer-kernel presentation for the bulk birthmark observable.
-- This shows why injective reconstruction of the whole bulk is unnecessary:
-- the quotient relevant to this declared consumer is equality of birthmark
-- outcomes, not equality of worlds.
------------------------------------------------------------------------

birthmarkConsumerKernelPresentation :
  (T : BirthmarkObservableTransport) →
  Kernel.ConsumerKernelPresentation (bulkBirthmark T)
birthmarkConsumerKernelPresentation T =
  Kernel.canonicalConsumerKernelPresentation (bulkBirthmark T)

record BirthmarkBoundarySufficiencyReceipt
    (T : BirthmarkObservableTransport) : Set₁ where
  field
    boundaryObservationIsConsumerSufficient :
      (left right : BulkState T) →
      toBoundary T left ≡ toBoundary T right →
      bulkBirthmark T left ≡ bulkBirthmark T right

canonicalBirthmarkBoundarySufficiency :
  (T : BirthmarkObservableTransport) →
  BirthmarkBoundarySufficiencyReceipt T
canonicalBirthmarkBoundarySufficiency T =
  record
    { boundaryObservationIsConsumerSufficient =
        boundaryEqualityPreservesBirthmark T
    }

------------------------------------------------------------------------
-- Promotion firewall.
------------------------------------------------------------------------

record BirthmarkTransportAuthorityBoundary : Set where
  constructor birthmarkTransportAuthorityBoundary
  field
    consumerSufficiencyIsEnoughForBirthmarkObservable : Bool
    birthmarkTransportDoesNotRequireBulkInjectivity : Bool
    observableTransportDoesNotIdentifyEntropy : Bool
    observableTransportDoesNotIdentifyResidualInformationDensity : Bool
    physicalBoundaryFactorizationStillRequired : Bool
    consumerSufficiencyDoesNotMeanWorldCompleteness : Bool

canonicalBirthmarkTransportAuthorityBoundary :
  BirthmarkTransportAuthorityBoundary
canonicalBirthmarkTransportAuthorityBoundary =
  birthmarkTransportAuthorityBoundary true true true true true true

consumerSufficiencyIsEnoughForBirthmarkObservable : Bool
consumerSufficiencyIsEnoughForBirthmarkObservable = true

birthmarkTransportDoesNotRequireBulkInjectivity : Bool
birthmarkTransportDoesNotRequireBulkInjectivity = true

observableTransportDoesNotIdentifyEntropy : Bool
observableTransportDoesNotIdentifyEntropy = true

observableTransportDoesNotIdentifyResidualInformationDensity : Bool
observableTransportDoesNotIdentifyResidualInformationDensity = true

physicalBoundaryFactorizationStillRequired : Bool
physicalBoundaryFactorizationStillRequired = true

birthmarkResidualTransportCompilerOwned : Bool
birthmarkResidualTransportCompilerOwned = true
