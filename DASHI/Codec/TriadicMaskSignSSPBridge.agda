module DASHI.Codec.TriadicMaskSignSSPBridge where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

open import DASHI.Algebra.Trit using (Trit)
open import DASHI.Codec.TriadicMaskSignFactorization
  using (FactorizedTrit; encodeTrit; decodeTrit; decode-encode; encode-decode)
open import DASHI.Foundations.SSPTritCarrier
  using (SSPTrit; toTrit; fromTrit; toTrit-fromTrit; fromTrit-toTrit)

------------------------------------------------------------------------
-- Reuse the established SSP/Base369 carrier rather than introducing a
-- second visual or semantic ternary alphabet.

encodeSSPTrit : SSPTrit → FactorizedTrit
encodeSSPTrit t = encodeTrit (toTrit t)

decodeSSPTrit : FactorizedTrit → SSPTrit
decodeSSPTrit f = fromTrit (decodeTrit f)

decodeSSP-encodeSSP : ∀ t → decodeSSPTrit (encodeSSPTrit t) ≡ t
decodeSSP-encodeSSP t
  rewrite decode-encode (toTrit t)
  = fromTrit-toTrit t

encodeSSP-decodeSSP : ∀ f → encodeSSPTrit (decodeSSPTrit f) ≡ f
encodeSSP-decodeSSP f
  rewrite toTrit-fromTrit (decodeTrit f)
  = encode-decode f

record TriadicMaskSignSSPReceipt : Set where
  constructor mkTriadicMaskSignSSPReceipt
  field
    sourceCarrier : Set
    factorCarrier : Set
    encode : sourceCarrier → factorCarrier
    decode : factorCarrier → sourceCarrier
    decodeEncode : ∀ t → decode (encode t) ≡ t
    encodeDecode : ∀ f → encode (decode f) ≡ f
    bridgeSummary : String

open TriadicMaskSignSSPReceipt public

canonicalTriadicMaskSignSSPReceipt : TriadicMaskSignSSPReceipt
canonicalTriadicMaskSignSSPReceipt =
  mkTriadicMaskSignSSPReceipt
    SSPTrit
    FactorizedTrit
    encodeSSPTrit
    decodeSSPTrit
    decodeSSP-encodeSSP
    encodeSSP-decodeSSP
    "Exact support/sign factorisation reusing the canonical SSPTrit -> Trit bridge; no parallel ternary carrier is introduced."
