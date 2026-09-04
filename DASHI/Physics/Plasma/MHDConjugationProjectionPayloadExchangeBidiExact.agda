module DASHI.Physics.Plasma.MHDConjugationProjectionPayloadExchangeBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- LITERAL MHD PRODUCER CUTSET FOR EXCHANGE-INVARIANT TRANSFER PAYLOADS.
--
-- The generic skew theorem only needs payloadForward = payloadReverse.  In a
-- Fourier/helical MHD application that equality must be produced from the
-- actual complex-conjugation/reality convention, transverse/Leray projection,
-- amplitude exchange and normalization used by the same triad.
------------------------------------------------------------------------

record MHDTransferPayloadExchange : Set₁ where
  constructor mhd-transfer-payload-exchange
  field
    Mode Polarisation Amplitude Payload : Set
    k p q : Mode
    a b c : Polarisation
    forwardAmplitude reverseAmplitude : Amplitude
    forwardPayload reversePayload : Payload

    sameLiteralTriadReceipt : Set
    exchangedOutputInputReceipt : Set
    amplitudeExchangeReceipt : Set
    conjugationRealityReceipt : Set
    transverseProjectionReceipt : Set
    pressureOrthogonalityReceipt : Set
    normalizationExchangeReceipt : Set

    payloadExchange : forwardPayload ≡ reversePayload
    payloadReference : String

open MHDTransferPayloadExchange public

record PayloadExchangeBidiBoundary : Set where
  constructor payload-exchange-bidi-boundary
  field
    realFieldRealityAloneProvesPayloadExchange : Bool
    realFieldRealityAloneProvesPayloadExchangeIsFalse :
      realFieldRealityAloneProvesPayloadExchange ≡ false

    transverseProjectionAloneProvesPayloadExchange : Bool
    transverseProjectionAloneProvesPayloadExchangeIsFalse :
      transverseProjectionAloneProvesPayloadExchange ≡ false

    allLiteralExchangeReceiptsCanPromotePayloadEquality : Bool
    allLiteralExchangeReceiptsCanPromotePayloadEqualityIsTrue :
      allLiteralExchangeReceiptsCanPromotePayloadEquality ≡ true

    payloadEqualityCanFeedGenericFullTransferSkew : Bool
    payloadEqualityCanFeedGenericFullTransferSkewIsTrue :
      payloadEqualityCanFeedGenericFullTransferSkew ≡ true

canonicalPayloadExchangeBidiBoundary : PayloadExchangeBidiBoundary
canonicalPayloadExchangeBidiBoundary =
  payload-exchange-bidi-boundary false refl false refl true refl true refl
