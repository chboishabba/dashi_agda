module DASHI.Physics.QuantumVacuum.PerfectConductorLongitudinalQuantisationHighestAlphaExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Analysis.EndpointZeroTrigonometricSeparationExact as Endpoint
import DASHI.Analysis.SineZeroClassificationSourceAuthorityExact as SineSource
import DASHI.Analysis.BishopNonzeroMultiplicationCancellationExact as BishopCancel
import DASHI.Analysis.BishopRightDivisionTransportExact as BishopDivide

------------------------------------------------------------------------
-- HIGHEST-ALPHA LONGITUDINAL QUANTISATION SPLIT
--
-- OWNED:
--   two endpoint-zero conditions reduce the separated trigonometric mode to
--   A sin(k d) = 0 and eliminate the cosine coefficient;
--   Bishop nonzero multiplication cancellation;
--   Bishop right-division transport by nonzero plate separation.
--
-- SOURCEBACKED:
--   DLMF classifies all sine zeros as integer multiples of pi.
--
-- LIVE:
--   transport that source-backed zero classification into the literal DASHI
--   constructive trigonometric object and weld its integer/pi coordinates to
--   the physical longitudinal mode index.  TE/TM completeness remains a
--   separate Maxwell theorem.
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
    bishopCancellationOwnerUsed : Set
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
    bishopDivisionTransportOwnerUsed : Set
    sameBishopScalarCarrier : Set
    kEqualsIntegerPiOverD : Set
    reading : String

open LongitudinalQuantisationCompletion public

record LongitudinalQuantisationStatus : Set where
  field
    endpointReductionOwned : Bool
    bishopAmplitudeCancellationOwned : Bool
    bishopDivisionTransportOwned : Bool
    sineZeroClassificationSourceBacked : Bool
    sineSourceTransportClosed : Bool
    physicalModeIndexWeldClosed : Bool

    endpointReductionOwnedIsTrue : endpointReductionOwned ≡ true
    bishopAmplitudeCancellationOwnedIsTrue : bishopAmplitudeCancellationOwned ≡ true
    bishopDivisionTransportOwnedIsTrue : bishopDivisionTransportOwned ≡ true
    sineZeroClassificationSourceBackedIsTrue :
      sineZeroClassificationSourceBacked ≡ true
    sineSourceTransportClosedIsFalse : sineSourceTransportClosed ≡ false
    physicalModeIndexWeldClosedIsFalse : physicalModeIndexWeldClosed ≡ false

open LongitudinalQuantisationStatus public

canonicalLongitudinalQuantisationStatus : LongitudinalQuantisationStatus
canonicalLongitudinalQuantisationStatus = record
  { endpointReductionOwned = true
  ; bishopAmplitudeCancellationOwned = true
  ; bishopDivisionTransportOwned = true
  ; sineZeroClassificationSourceBacked = true
  ; sineSourceTransportClosed = false
  ; physicalModeIndexWeldClosed = false
  ; endpointReductionOwnedIsTrue = refl
  ; bishopAmplitudeCancellationOwnedIsTrue = refl
  ; bishopDivisionTransportOwnedIsTrue = refl
  ; sineZeroClassificationSourceBackedIsTrue = refl
  ; sineSourceTransportClosedIsFalse = refl
  ; physicalModeIndexWeldClosedIsFalse = refl
  }
