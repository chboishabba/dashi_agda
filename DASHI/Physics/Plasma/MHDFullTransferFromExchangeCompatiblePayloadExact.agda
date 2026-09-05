module DASHI.Physics.Plasma.MHDFullTransferFromExchangeCompatiblePayloadExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field

------------------------------------------------------------------------
-- FULL TRANSFER FROM AN EXCHANGE-ANTISYMMETRIC COUPLING AND AN
-- EXCHANGE-INVARIANT PAYLOAD.
--
-- This is the application-neutral algebra needed by the helical-Elsasser MHD
-- lane.  Complex conjugation, reality, projection and normalisation are not
-- assumed here; they are producers of the payloadExchange receipt in the
-- literal MHD application.
------------------------------------------------------------------------

private
  sub : ∀ {r} {F : C3.RealField r} → C3.Carrier F → C3.Carrier F → C3.Carrier F
  sub {F = F} x y = C3.add F x (C3.negate F y)

record ExchangeCompatibleTransfer {r : _} (F : C3.RealField r) : Set r where
  constructor exchange-compatible-transfer
  field
    couplingForward couplingReverse : C3.Carrier F
    payloadForward payloadReverse : C3.Carrier F
    couplingExchange : couplingForward ≡ C3.negate F couplingReverse
    payloadExchange : payloadForward ≡ payloadReverse
    payloadReference : String

open ExchangeCompatibleTransfer public

forwardTransfer :
  ∀ {r} {F : C3.RealField r} →
  ExchangeCompatibleTransfer F → C3.Carrier F
forwardTransfer {F = F} x =
  C3.multiply F (couplingForward x) (payloadForward x)

reverseTransfer :
  ∀ {r} {F : C3.RealField r} →
  ExchangeCompatibleTransfer F → C3.Carrier F
reverseTransfer {F = F} x =
  C3.multiply F (couplingReverse x) (payloadReverse x)

fullTransferExchangeAntisymmetry :
  ∀ {r} {F : C3.RealField r}
    (x : ExchangeCompatibleTransfer F) →
  forwardTransfer x ≡ C3.negate F (reverseTransfer x)
fullTransferExchangeAntisymmetry {F = F} x
  rewrite couplingExchange x | payloadExchange x =
  R.solve 2
    (λ c p → (((R.⊝ c) R.⊗ p) R.⊜ (R.⊝ (c R.⊗ p))))
    refl (couplingReverse x) (payloadReverse x)
  where module R = Field.Solver F

pairTransferCancels :
  ∀ {r} {F : C3.RealField r}
    (x : ExchangeCompatibleTransfer F) →
  C3.add F (forwardTransfer x) (reverseTransfer x) ≡ C3.zero F
pairTransferCancels {F = F} x
  rewrite fullTransferExchangeAntisymmetry x =
  R.solve 1
    (λ t → (((R.⊝ t) R.⊕ t) R.⊜ R.Κ (C3.zero F)))
    refl (reverseTransfer x)
  where module R = Field.Solver F

record ExchangeCompatibleTransferBoundary : Set where
  constructor exchange-compatible-transfer-boundary
  field
    couplingSkewWithoutPayloadExchangeIsEnough : Bool
    couplingSkewWithoutPayloadExchangeIsEnoughIsFalse :
      couplingSkewWithoutPayloadExchangeIsEnough ≡ false

    exchangeCompatiblePayloadPromotesFullTransferSkew : Bool
    exchangeCompatiblePayloadPromotesFullTransferSkewIsTrue :
      exchangeCompatiblePayloadPromotesFullTransferSkew ≡ true

    fullTransferSkewPromotesPairCancellationBeforeNorm : Bool
    fullTransferSkewPromotesPairCancellationBeforeNormIsTrue :
      fullTransferSkewPromotesPairCancellationBeforeNorm ≡ true

canonicalExchangeCompatibleTransferBoundary : ExchangeCompatibleTransferBoundary
canonicalExchangeCompatibleTransferBoundary =
  exchange-compatible-transfer-boundary false refl true refl true refl
