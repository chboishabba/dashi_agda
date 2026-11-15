module DASHI.Physics.Closure.ZhengKolkowitz2023TransportAttemptReceiptExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.ZhengKolkowitz2023PublicDataReceiptExact as Public

------------------------------------------------------------------------
-- DATED TRANSPORT EVENT FOR THE ZHENG/KOLKOWITZ PUBLIC DATASET
--
-- This is intentionally narrower than a generic artifact-transport ontology.
-- It records one acquisition attempt against a source-paid public manifest.
-- Inspired by the transport/identity separation visible in repository work,
-- but without importing an unmerged sibling PR as theorem authority.
--
-- Source authority:
--   Zenodo DOI 10.5281/zenodo.8184043 owns the record and file manifest.
-- DASHI authority:
--   the execution observation that this runtime resolved the manifest but did
--   not successfully materialise the payload bytes on 2026-10-17.
--
-- Failure of one transport path does not invalidate the source manifest and
-- does not become an empirical result about the experiment.
------------------------------------------------------------------------

record ZhengTransportAttemptReceipt : Set where
  field
    publicDataReceipt : Public.ZhengKolkowitz2023PublicDataReceipt
    publicDataReceiptIsCanonical :
      publicDataReceipt ≡ Public.canonicalZhengKolkowitz2023PublicDataReceipt

    sourceDOI : String
    attemptDate : String
    transportSurfaces : List String
    failureObservation : String

    manifestResolved : Bool
    manifestResolvedIsTrue : manifestResolved ≡ true

    payloadTransportSucceeded : Bool
    payloadTransportSucceededIsFalse : payloadTransportSucceeded ≡ false

    payloadBytesMaterialised : Bool
    payloadBytesMaterialisedIsFalse : payloadBytesMaterialised ≡ false

    payloadDigestVerified : Bool
    payloadDigestVerifiedIsFalse : payloadDigestVerified ≡ false

    transportAttemptEstablishesEmpiricalResult : Bool
    transportAttemptEstablishesEmpiricalResultIsFalse :
      transportAttemptEstablishesEmpiricalResult ≡ false

    transportFailureInvalidatesSourceManifest : Bool
    transportFailureInvalidatesSourceManifestIsFalse :
      transportFailureInvalidatesSourceManifest ≡ false

    reading : List String

open ZhengTransportAttemptReceipt public

canonicalZhengTransportAttemptReceipt : ZhengTransportAttemptReceipt
canonicalZhengTransportAttemptReceipt = record
  { publicDataReceipt = Public.canonicalZhengKolkowitz2023PublicDataReceipt
  ; publicDataReceiptIsCanonical = refl
  ; sourceDOI = "10.5281/zenodo.8184043"
  ; attemptDate = "2026-10-17"
  ; transportSurfaces =
      "Zenodo HTML record/file manifest"
      ∷ "web file-download links"
      ∷ "container raw download"
      ∷ []
  ; failureObservation =
      "web file links returned cache-miss / HTTP 429 and container download failed"
  ; manifestResolved = true
  ; manifestResolvedIsTrue = refl
  ; payloadTransportSucceeded = false
  ; payloadTransportSucceededIsFalse = refl
  ; payloadBytesMaterialised = false
  ; payloadBytesMaterialisedIsFalse = refl
  ; payloadDigestVerified = false
  ; payloadDigestVerifiedIsFalse = refl
  ; transportAttemptEstablishesEmpiricalResult = false
  ; transportAttemptEstablishesEmpiricalResultIsFalse = refl
  ; transportFailureInvalidatesSourceManifest = false
  ; transportFailureInvalidatesSourceManifestIsFalse = refl
  ; reading =
      "The Zenodo record resolved and independently exposed the four source-published file identities and MD5 values already recorded in the public-data receipt."
      ∷ "The payload endpoints did not yield usable CSV bytes through the current execution surfaces, so byte materialisation and digest verification remain false."
      ∷ "Transport failure is an execution-environment observation, not evidence against the Zenodo manifest or against the experimental result."
      ∷ "A later successful transport event should be represented by a successor receipt rather than rewriting this failed attempt."
      ∷ []
  }

canonicalManifestResolved : manifestResolved canonicalZhengTransportAttemptReceipt ≡ true
canonicalManifestResolved = refl

canonicalPayloadStillNotMaterialised :
  payloadBytesMaterialised canonicalZhengTransportAttemptReceipt ≡ false
canonicalPayloadStillNotMaterialised = refl
