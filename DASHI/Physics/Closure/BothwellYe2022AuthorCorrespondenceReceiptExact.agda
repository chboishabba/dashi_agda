module DASHI.Physics.Closure.BothwellYe2022AuthorCorrespondenceReceiptExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.BothwellYe2022ExternalAcquisitionMaxCut as Acquisition

------------------------------------------------------------------------
-- PROVIDER-BACKED CORRESPONDENCE EVENT RECEIPT
--
-- The acquisition packet owner records the state when the request was only
-- constructed. This later event records that the request was actually sent.
-- It is deliberately additive/revisable: historical construction state is not
-- rewritten after the fact.
--
-- Authority boundary:
--   * Gmail sent-mail state supports only the fact of outbound correspondence.
--   * it does not establish delivery/read status, author response, source truth,
--     data/code acquisition, replay success, or empirical acceptance.
------------------------------------------------------------------------

record AuthorRequestSendReceipt : Set where
  field
    acquisitionPacket : Acquisition.BothwellYe2022ExternalAcquisitionMaxCut
    acquisitionPacketIsCanonical :
      acquisitionPacket ≡ Acquisition.canonicalBothwellYe2022ExternalAcquisitionMaxCut

    sendProvider : String
    sentLocalTimestamp : String
    subject : String
    recipients : List String

    providerVerifiedSent : Bool
    providerVerifiedSentIsTrue : providerVerifiedSent ≡ true

    authorRequestSent : Bool
    authorRequestSentIsTrue : authorRequestSent ≡ true

    authorReplyReceived : Bool
    authorReplyReceivedIsFalse : authorReplyReceived ≡ false

    sendReceiptIsExperimentalEvidence : Bool
    sendReceiptIsExperimentalEvidenceIsFalse :
      sendReceiptIsExperimentalEvidence ≡ false

    rawExperimentArraysAcquired : Bool
    rawExperimentArraysAcquiredIsFalse : rawExperimentArraysAcquired ≡ false

    analysisCodeAcquired : Bool
    analysisCodeAcquiredIsFalse : analysisCodeAcquired ≡ false

    deliveryOrReadConfirmed : Bool
    deliveryOrReadConfirmedIsFalse : deliveryOrReadConfirmed ≡ false

    reading : List String

open AuthorRequestSendReceipt public

canonicalBothwellYe2022AuthorRequestSendReceipt : AuthorRequestSendReceipt
canonicalBothwellYe2022AuthorRequestSendReceipt = record
  { acquisitionPacket = Acquisition.canonicalBothwellYe2022ExternalAcquisitionMaxCut
  ; acquisitionPacketIsCanonical = refl
  ; sendProvider = "Gmail sent mailbox"
  ; sentLocalTimestamp = "2026-10-16T12:30:17+10:00"
  ; subject = "Data/code request: Bothwell et al. 2022 gravitational redshift analysis"
  ; recipients =
      "tobias.bothwell@colorado.edu"
      ∷ "ye@jila.colorado.edu"
      ∷ []
  ; providerVerifiedSent = true
  ; providerVerifiedSentIsTrue = refl
  ; authorRequestSent = true
  ; authorRequestSentIsTrue = refl
  ; authorReplyReceived = false
  ; authorReplyReceivedIsFalse = refl
  ; sendReceiptIsExperimentalEvidence = false
  ; sendReceiptIsExperimentalEvidenceIsFalse = refl
  ; rawExperimentArraysAcquired = false
  ; rawExperimentArraysAcquiredIsFalse = refl
  ; analysisCodeAcquired = false
  ; analysisCodeAcquiredIsFalse = refl
  ; deliveryOrReadConfirmed = false
  ; deliveryOrReadConfirmedIsFalse = refl
  ; reading =
      "The typed Bothwell/Ye data-and-code request was sent to both listed corresponding-author endpoints and is present in the sender's Gmail Sent mailbox."
      ∷ "The send event advances correspondence state only; it is not an author reply, experimental evidence, data acquisition, code acquisition, replay, or empirical acceptance."
      ∷ "The earlier request-packet owner remains a truthful historical construction-state receipt instead of being rewritten after this later event."
      ∷ []
  }

canonicalAuthorRequestSent :
  authorRequestSent canonicalBothwellYe2022AuthorRequestSendReceipt ≡ true
canonicalAuthorRequestSent = refl

canonicalAuthorReplyStillPending :
  authorReplyReceived canonicalBothwellYe2022AuthorRequestSendReceipt ≡ false
canonicalAuthorReplyStillPending = refl

canonicalSendIsNotExperimentalEvidence :
  sendReceiptIsExperimentalEvidence canonicalBothwellYe2022AuthorRequestSendReceipt ≡ false
canonicalSendIsNotExperimentalEvidence = refl
