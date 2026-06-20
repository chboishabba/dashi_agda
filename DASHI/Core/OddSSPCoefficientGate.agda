module DASHI.Core.OddSSPCoefficientGate where

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Core.SuperSSPOddPayload using
  ( SuperSSPOddPayload
  ; canonicalSuperSSPOddPayload
  ; payloadBodySurface
  ; payloadOddResidueSurface
  )
open import DASHI.Foundations.FifteenSSPSurface using
  ( FifteenSSPSurface )

------------------------------------------------------------------------
-- Typed odd SSP coefficient gate.
--
-- For a one-generator odd payload `A + B theta`, all three operations
-- return the same typed odd 15SSP residual surface `B`.

oddCoeffExtractor :
  SuperSSPOddPayload →
  FifteenSSPSurface
oddCoeffExtractor =
  payloadOddResidueSurface

oddDerivative :
  SuperSSPOddPayload →
  FifteenSSPSurface
oddDerivative =
  payloadOddResidueSurface

berezinIntegral :
  SuperSSPOddPayload →
  FifteenSSPSurface
berezinIntegral =
  payloadOddResidueSurface

record OddSSPCoefficientGateReceipt : Set where
  constructor mkOddSSPCoefficientGateReceipt
  field
    payload :
      SuperSSPOddPayload

    bodyProjection :
      FifteenSSPSurface

    oddProjection :
      FifteenSSPSurface

    bodyProjectionMatches :
      bodyProjection ≡ payloadBodySurface payload

    oddProjectionMatches :
      oddProjection ≡ payloadOddResidueSurface payload

    extractorMatchesOddProjection :
      oddCoeffExtractor payload ≡ oddProjection

    derivativeMatchesOddProjection :
      oddDerivative payload ≡ oddProjection

    integralMatchesOddProjection :
      berezinIntegral payload ≡ oddProjection

open OddSSPCoefficientGateReceipt public

canonicalOddSSPCoefficientGateReceipt :
  OddSSPCoefficientGateReceipt
canonicalOddSSPCoefficientGateReceipt =
  mkOddSSPCoefficientGateReceipt
    canonicalSuperSSPOddPayload
    (payloadBodySurface canonicalSuperSSPOddPayload)
    (payloadOddResidueSurface canonicalSuperSSPOddPayload)
    refl
    refl
    refl
    refl
    refl

oddCoeffExtractorIsOddCoefficient :
  oddCoeffExtractor canonicalSuperSSPOddPayload
  ≡
  payloadOddResidueSurface canonicalSuperSSPOddPayload
oddCoeffExtractorIsOddCoefficient =
  refl

oddDerivativeCollapsesToOddCoeffExtractor :
  oddDerivative canonicalSuperSSPOddPayload
  ≡
  oddCoeffExtractor canonicalSuperSSPOddPayload
oddDerivativeCollapsesToOddCoeffExtractor =
  refl

berezinIntegralCollapsesToOddCoeffExtractor :
  berezinIntegral canonicalSuperSSPOddPayload
  ≡
  oddCoeffExtractor canonicalSuperSSPOddPayload
berezinIntegralCollapsesToOddCoeffExtractor =
  refl

oddDerivativeCollapsesToBerezinIntegral :
  oddDerivative canonicalSuperSSPOddPayload
  ≡
  berezinIntegral canonicalSuperSSPOddPayload
oddDerivativeCollapsesToBerezinIntegral =
  refl
