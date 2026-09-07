module DASHI.Wikimedia.SLRWikimediaHandoffABIExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.String using (String)

import DASHI.Wikimedia.SensibLawSourceUnitReviewHandoffExact as Handoff

------------------------------------------------------------------------
-- SLR / RUST CONSUMER ABI
--
-- Current slr/main README contract inspected 7 Sep 2026:
--   * sensiblaw-core owns revision-scoped spans and promotion receipt types;
--   * sensiblaw-stream consumes parser observations and emits residuals;
--   * parser sidecars never own canonical semantic state;
--   * Rust owns deterministic compilation/publication boundaries.
--
-- This compiler lets SLR consume the generic SensibLaw review packet without
-- redefining Nat/Climate or Wikimedia source semantics.
------------------------------------------------------------------------

slrMainReference : String
slrMainReference = "chboishabba/slr main README inspected 2026-09-07"

handoffToSlr : Handoff.SensibLawReviewPacket → Handoff.RuntimeHandoffReceipt
handoffToSlr packet =
  Handoff.runtime-handoff-receipt
    Handoff.slrRustRuntime
    (Handoff.sourceUnitId (Handoff.sourceUnit packet))
    (Handoff.packetId packet)
    slrMainReference
    true refl
    true refl
    false refl
    false refl

slrConsumerExact :
  (packet : Handoff.SensibLawReviewPacket) →
  Handoff.consumer (handoffToSlr packet) ≡ Handoff.slrRustRuntime
slrConsumerExact packet = refl

slrDoesNotOwnAuthority :
  (packet : Handoff.SensibLawReviewPacket) →
  Handoff.runtimeOwnsSourceAuthority (handoffToSlr packet) ≡ false
slrDoesNotOwnAuthority packet = refl

slrDoesNotOwnPromotionFromConsumption :
  (packet : Handoff.SensibLawReviewPacket) →
  Handoff.runtimeOwnsSemanticPromotion (handoffToSlr packet) ≡ false
slrDoesNotOwnPromotionFromConsumption packet = refl

-- Rust implementation of the carrier is not evidence that the carrier's
-- source propositions are true, admissible, or migration-safe.
data RustABIImplementsSourceAuthority : Set where
data RustABIImplementsMigrationDecision : Set where
data ParserSpanCreatesPromotionReceipt : Set where

rustAbiDoesNotImplementSourceAuthority : RustABIImplementsSourceAuthority → ⊥
rustAbiDoesNotImplementSourceAuthority ()

rustAbiDoesNotChooseMigrationByItself : RustABIImplementsMigrationDecision → ⊥
rustAbiDoesNotChooseMigrationByItself ()

parserSpanDoesNotCreatePromotionReceipt : ParserSpanCreatesPromotionReceipt → ⊥
parserSpanDoesNotCreatePromotionReceipt ()
