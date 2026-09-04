module DASHI.Physics.QuantumVacuum.PerfectConductorLongitudinalQuantisationHighestAlphaExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Analysis.EndpointZeroTrigonometricSeparationExact as Endpoint
import DASHI.Analysis.SineZeroClassificationSourceAuthorityExact as SineSource

------------------------------------------------------------------------
-- HIGHEST-ALPHA LONGITUDINAL QUANTISATION SPLIT
--
-- OWNED:
--   two endpoint-zero conditions reduce the separated trigonometric mode to
--   A sin(k d) = 0 and eliminate the cosine coefficient.
--
-- SOURCEBACKED:
--   DLMF classifies all sine zeros as integer multiples of pi.
--
-- LIVE:
--   instantiate nonzero-amplitude cancellation on the literal electromagnetic
--   mode carrier and transport the source-backed zero classification into the
--   repo's constructive-real/trigonometric object; then divide by d on the same
--   scalar carrier to obtain k = n*pi/d.
------------------------------------------------------------------------

record NonzeroAmplitudeCancellation : Set₁ where
  field
    Scalar : Set
    zero : Scalar
    multiply : Scalar → Scalar → Scalar
    Nonzero : Scalar → Set
    cancelToRightZero :
      (A x : Scalar) →
      Nonzero A →
      multiply A x ≡ zero →
      x ≡ zero
    reading : String

open NonzeroAmplitudeCancellation public

record LongitudinalSineZeroWeld : Set₁ where
  field
    endpointReductionOwnerUsed : Set
    nonzeroAmplitudeCancellation : NonzeroAmplitudeCancellation
    sameAmplitudeAsPhysicalMode : Set
    sameSineAsConstructiveTrigAuthority : Set
    sameKdArgument : Set
    sourceAuthority : SineSource.SineZeroClassificationSourceAuthority
    sourceClassificationTransport : Set
    reading : String

open LongitudinalSineZeroWeld public

record LongitudinalQuantisationCompletion : Set₁ where
  field
    weld : LongitudinalSineZeroWeld
    IntegerIndex : Set
    index : IntegerIndex
    Scalar : Set
    k d pi : Scalar
    integerTimesPi : IntegerIndex → Scalar → Scalar
    divideBySeparation : Scalar → Scalar → Scalar

    kdEqualsIntegerPi : Set
    separationNonzero : Set
    divisionTransport : Set
    kEqualsIntegerPiOverD : Set
    reading : String

open LongitudinalQuantisationCompletion public

record LongitudinalQuantisationStatus : Set where
  field
    endpointReductionOwned : Bool
    sineZeroClassificationSourceBacked : Bool
    nonzeroAmplitudeCancellationClosed : Bool
    sineSourceTransportClosed : Bool
    divideBySeparationClosed : Bool

    endpointReductionOwnedIsTrue : endpointReductionOwned ≡ true
    sineZeroClassificationSourceBackedIsTrue :
      sineZeroClassificationSourceBacked ≡ true
    nonzeroAmplitudeCancellationClosedIsFalse :
      nonzeroAmplitudeCancellationClosed ≡ false
    sineSourceTransportClosedIsFalse : sineSourceTransportClosed ≡ false
    divideBySeparationClosedIsFalse : divideBySeparationClosed ≡ false

open LongitudinalQuantisationStatus public

canonicalLongitudinalQuantisationStatus : LongitudinalQuantisationStatus
canonicalLongitudinalQuantisationStatus = record
  { endpointReductionOwned = true
  ; sineZeroClassificationSourceBacked = true
  ; nonzeroAmplitudeCancellationClosed = false
  ; sineSourceTransportClosed = false
  ; divideBySeparationClosed = false
  ; endpointReductionOwnedIsTrue = refl
  ; sineZeroClassificationSourceBackedIsTrue = refl
  ; nonzeroAmplitudeCancellationClosedIsFalse = refl
  ; sineSourceTransportClosedIsFalse = refl
  ; divideBySeparationClosedIsFalse = refl
  }
