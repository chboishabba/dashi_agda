module DASHI.Context.PublicPowerContextBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

open import DASHI.Context.ContextEnvelopeInvariant
open import DASHI.Context.NarrativeProjectionBoundary

------------------------------------------------------------------------
-- Public figures and governing teams use the same invariant at a different
-- scale: preserve the person, promise, authority, attempt, obstruction, and
-- outcome without flattening them into a PR narrative or moral verdict.


data AuthorityMode : Set where
  directAuthority : AuthorityMode
  boardAppointmentAuthority : AuthorityMode
  coalitionRequired : AuthorityMode
  statePartnershipRequired : AuthorityMode
  noAuthority : AuthorityMode
  authorityUnknown : AuthorityMode


data DeliveryState : Set where
  promised : DeliveryState
  planned : DeliveryState
  attempted : DeliveryState
  partiallyDelivered : DeliveryState
  delivered : DeliveryState
  blocked : DeliveryState
  failedAfterAttempt : DeliveryState
  notAttempted : DeliveryState
  statusUnknown : DeliveryState


data TrustScale : Set where
  microTrust : TrustScale
  macroTrust : TrustScale

record PublicPromise : Set where
  field
    promiseId : String
    canonicalPromiseText : String
    context : ContextEnvelope
    authorityMode : AuthorityMode
    deliveryState : DeliveryState
    trustScale : TrustScale
    evidenceArtifactIds : List String
    blockerArtifactIds : List String

    promiseContextRetained : Bool
    promiseContextRetainedIsTrue : promiseContextRetained ≡ true

    attemptVisible : Bool
    attemptVisibleIsTrue : attemptVisible ≡ true

    obstructionVisibleWhenEvidenced : Bool
    obstructionVisibleWhenEvidencedIsTrue :
      obstructionVisibleWhenEvidenced ≡ true

    failureNotAutomaticallyMoralised : Bool
    failureNotAutomaticallyMoralisedIsTrue :
      failureNotAutomaticallyMoralised ≡ true

open PublicPromise public

record PublicConversationUse : Set where
  field
    source : ContextBoundArtifact
    excerptProjection : NarrativeProjection

    originalVenueRetained : Bool
    originalVenueRetainedIsTrue : originalVenueRetained ≡ true

    originalAudienceRetained : Bool
    originalAudienceRetainedIsTrue : originalAudienceRetained ≡ true

    comedicFrameMayBeDeclared : Bool
    comedicFrameMayBeDeclaredIsTrue : comedicFrameMayBeDeclared ≡ true

    clipIsNotWholePerson : Bool
    clipIsNotWholePersonIsTrue : clipIsNotWholePerson ≡ true

open PublicConversationUse public

record SmallTrustLedger : Set where
  field
    entries : List PublicPromise

    microPromisesAreFirstClass : Bool
    microPromisesAreFirstClassIsTrue :
      microPromisesAreFirstClass ≡ true

    unresolvedSmallPromisesRemainVisible : Bool
    unresolvedSmallPromisesRemainVisibleIsTrue :
      unresolvedSmallPromisesRemainVisible ≡ true

    macroAgendaDoesNotEraseMicroFailure : Bool
    macroAgendaDoesNotEraseMicroFailureIsTrue :
      macroAgendaDoesNotEraseMicroFailure ≡ true

open SmallTrustLedger public

promiseRetainsContext :
  (p : PublicPromise) →
  promiseContextRetained p ≡ true
promiseRetainsContext p = promiseContextRetainedIsTrue p

canonicalEmptySmallTrustLedger : SmallTrustLedger
canonicalEmptySmallTrustLedger =
  record
    { entries = []
    ; microPromisesAreFirstClass = true
    ; microPromisesAreFirstClassIsTrue = refl
    ; unresolvedSmallPromisesRemainVisible = true
    ; unresolvedSmallPromisesRemainVisibleIsTrue = refl
    ; macroAgendaDoesNotEraseMicroFailure = true
    ; macroAgendaDoesNotEraseMicroFailureIsTrue = refl
    }
