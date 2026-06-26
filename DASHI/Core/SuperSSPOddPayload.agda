module DASHI.Core.SuperSSPOddPayload where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

open import DASHI.Foundations.FifteenSSPSurface using
  ( FifteenSSPSurface
  ; canonicalZeroFifteenSSPSurface
  ; canonicalPositiveFifteenSSPSurface
  ; canonicalNegativeFifteenSSPSurface
  ; canonicalExampleFifteenSSPSurface
  )

------------------------------------------------------------------------
-- Typed one-generator SuperSSP payload.
--
-- The even body and odd residue are both typed 15SSP trit surfaces.

record SuperSSPOddPayload : Set where
  constructor mkSuperSSPOddPayload
  field
    payloadLabel :
      String

    expansionLabel :
      String

    evenBody :
      FifteenSSPSurface

    oddResidue :
      FifteenSSPSurface

    candidateOnly :
      Bool

    candidateOnlyIsTrue :
      candidateOnly ≡ true

    promoted :
      Bool

    promotedIsFalse :
      promoted ≡ false

open SuperSSPOddPayload public

payloadBodySurface :
  SuperSSPOddPayload →
  FifteenSSPSurface
payloadBodySurface =
  evenBody

payloadOddResidueSurface :
  SuperSSPOddPayload →
  FifteenSSPSurface
payloadOddResidueSurface =
  oddResidue

payloadExpansion :
  SuperSSPOddPayload →
  String
payloadExpansion =
  expansionLabel

canonicalSuperSSPOddPayload :
  SuperSSPOddPayload
canonicalSuperSSPOddPayload =
  mkSuperSSPOddPayload
    "SuperSSP payload"
    "A + B theta"
    canonicalExampleFifteenSSPSurface
    canonicalNegativeFifteenSSPSurface
    true
    refl
    false
    refl

canonicalBalancedSuperSSPOddPayload :
  SuperSSPOddPayload
canonicalBalancedSuperSSPOddPayload =
  mkSuperSSPOddPayload
    "Balanced SuperSSP payload"
    "A_balanced + B_balanced theta"
    canonicalZeroFifteenSSPSurface
    canonicalPositiveFifteenSSPSurface
    true
    refl
    false
    refl

canonicalSuperSSPOddPayloadExamples :
  List SuperSSPOddPayload
canonicalSuperSSPOddPayloadExamples =
  canonicalSuperSSPOddPayload
  ∷ canonicalBalancedSuperSSPOddPayload
  ∷ []

canonicalPayloadBodyProjection :
  payloadBodySurface canonicalSuperSSPOddPayload
  ≡
  canonicalExampleFifteenSSPSurface
canonicalPayloadBodyProjection =
  refl

canonicalPayloadOddProjection :
  payloadOddResidueSurface canonicalSuperSSPOddPayload
  ≡
  canonicalNegativeFifteenSSPSurface
canonicalPayloadOddProjection =
  refl

balancedPayloadBodyProjection :
  payloadBodySurface canonicalBalancedSuperSSPOddPayload
  ≡
  canonicalZeroFifteenSSPSurface
balancedPayloadBodyProjection =
  refl

balancedPayloadOddProjection :
  payloadOddResidueSurface canonicalBalancedSuperSSPOddPayload
  ≡
  canonicalPositiveFifteenSSPSurface
balancedPayloadOddProjection =
  refl

canonicalPayloadExpansionIsCanonical :
  payloadExpansion canonicalSuperSSPOddPayload
  ≡
  "A + B theta"
canonicalPayloadExpansionIsCanonical =
  refl
