module DASHI.Analysis.CertifiedFiniteCarrierReindexExact where

------------------------------------------------------------------------
-- CERTIFIED FINITE CARRIER / EXACT REINDEX BOUNDARY
--
-- Cross-pollination from the Erdos factor-pair and exact-shell lanes:
-- estimates belong on the already-certified literal carrier.  Reindexing may
-- change presentation (for example residual-major -> factor-major, or selected
-- zero-major -> taper-major), but must not manufacture or erase carrier members.
--
-- This owner supplies the exact equivalence boundary only.  Domain consumers
-- still prove that their concrete filtered grid / selected-zero family inhabits it.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

record ExactCarrierReindex : Set₁ where
  field
    Carrier MajorCarrier : Set
    encode : Carrier → MajorCarrier
    decode : MajorCarrier → Carrier
    decodeEncode : (x : Carrier) → decode (encode x) ≡ x
    encodeDecode : (y : MajorCarrier) → encode (decode y) ≡ y
    boundedReading : String

open ExactCarrierReindex public

record CertifiedCarrierConsumer
    (r : ExactCarrierReindex) : Set₁ where
  field
    Payload : Set
    literalPayload : Carrier r → Payload
    reindexedPayload : MajorCarrier r → Payload
    payloadTransport : (y : MajorCarrier r) →
      reindexedPayload y ≡ literalPayload (decode r y)
    noNewCarrierElements : Set
    noCarrierElementsLost : Set
    boundedReading : String

open CertifiedCarrierConsumer public

------------------------------------------------------------------------
-- Tiny exact finite witness: Bool reindexed by swapping the two coordinates.
------------------------------------------------------------------------

swapBool : Bool → Bool
swapBool false = true
swapBool true = false

swapBoolInvolutive : (b : Bool) → swapBool (swapBool b) ≡ b
swapBoolInvolutive false = refl
swapBoolInvolutive true = refl

boolSwapReindex : ExactCarrierReindex
boolSwapReindex = record
  { Carrier = Bool
  ; MajorCarrier = Bool
  ; encode = swapBool
  ; decode = swapBool
  ; decodeEncode = swapBoolInvolutive
  ; encodeDecode = swapBoolInvolutive
  ; boundedReading =
      "Finite regression: an exact permutation changes presentation only; applying the inverse recovers the original certified carrier element."
  }

record CertifiedCarrierReindexBoundary : Set where
  constructor certified-carrier-reindex-boundary
  field
    estimateParallelAbstractCarrierInstead : Bool
    estimateParallelAbstractCarrierInsteadIsFalse :
      estimateParallelAbstractCarrierInstead ≡ false
    exactReindexBeforeInnerEstimatePreferred : Bool
    exactReindexBeforeInnerEstimatePreferredIsTrue :
      exactReindexBeforeInnerEstimatePreferred ≡ true
    multiZeroConcreteCarrierConstructedHere : Bool
    multiZeroConcreteCarrierConstructedHereIsFalse :
      multiZeroConcreteCarrierConstructedHere ≡ false

canonicalCertifiedCarrierReindexBoundary : CertifiedCarrierReindexBoundary
canonicalCertifiedCarrierReindexBoundary =
  certified-carrier-reindex-boundary false refl true refl false refl
