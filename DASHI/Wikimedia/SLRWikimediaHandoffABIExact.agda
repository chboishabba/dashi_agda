module DASHI.Wikimedia.SLRWikimediaHandoffABIExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Wikimedia.SensibLawSourceUnitReviewHandoffExact as Handoff
import DASHI.Wikimedia.SensibLawBoundaryArtifactMorphismExact as Morph

------------------------------------------------------------------------
-- SLR / RUST CONSUMER ABI
--
-- Current slr/main README contract inspected 7 Sep 2026 at the then-current
-- main repository state: sensiblaw-core owns revision-scoped spans/promotion
-- receipt types; sensiblaw-stream consumes parser observations/residuals;
-- parser sidecars do not own canonical semantic state; Rust owns deterministic
-- compilation/publication boundaries.
------------------------------------------------------------------------

slrMainReference : String
slrMainReference = "chboishabba/slr main README inspected 2026-09-07; repository main source surface"

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

------------------------------------------------------------------------
-- Earlier handoff point: SourceUnit -> ObservationClaimPayload -> SLR.
------------------------------------------------------------------------

record SlrObservationHandoffReceipt : Set where
  constructor slr-observation-handoff-receipt
  field
    extraction : Morph.ObservationExtractionReceipt
    observationReference : String
    sourceUnitReference : String
    consumerContractReference : String
    sourceIdentityPreserved : Bool
    sourceIdentityPreservedIsTrue : sourceIdentityPreserved ≡ true
    anchorsPreserved : Bool
    anchorsPreservedIsTrue : anchorsPreserved ≡ true
    slrOwnsSourceAuthority : Bool
    slrOwnsSourceAuthorityIsFalse : slrOwnsSourceAuthority ≡ false
    slrOwnsSemanticPromotion : Bool
    slrOwnsSemanticPromotionIsFalse : slrOwnsSemanticPromotion ≡ false
open SlrObservationHandoffReceipt public

observationToSlr : Morph.ObservationExtractionReceipt → SlrObservationHandoffReceipt
observationToSlr receipt =
  slr-observation-handoff-receipt
    receipt
    (Morph.observationId (Morph.payload receipt))
    (Handoff.sourceUnitId (Morph.sourceUnit (Morph.payload receipt)))
    slrMainReference
    true refl
    true refl
    false refl
    false refl

observationSourceIdentityPreserved :
  (receipt : Morph.ObservationExtractionReceipt) →
  sourceUnitReference (observationToSlr receipt)
  ≡ Handoff.sourceUnitId (Morph.sourceUnit (Morph.payload receipt))
observationSourceIdentityPreserved receipt = refl

observationHandoffDoesNotCreateAuthority :
  (receipt : Morph.ObservationExtractionReceipt) →
  slrOwnsSourceAuthority (observationToSlr receipt) ≡ false
observationHandoffDoesNotCreateAuthority receipt = refl

observationHandoffDoesNotCreatePromotion :
  (receipt : Morph.ObservationExtractionReceipt) →
  slrOwnsSemanticPromotion (observationToSlr receipt) ≡ false
observationHandoffDoesNotCreatePromotion receipt = refl

data RustABIImplementsSourceAuthority : Set where
data RustABIImplementsMigrationDecision : Set where
data ParserSpanCreatesPromotionReceipt : Set where
data ObservationConsumerCreatesCanonicalTruth : Set where

rustAbiDoesNotImplementSourceAuthority : RustABIImplementsSourceAuthority → ⊥
rustAbiDoesNotImplementSourceAuthority ()
rustAbiDoesNotChooseMigrationByItself : RustABIImplementsMigrationDecision → ⊥
rustAbiDoesNotChooseMigrationByItself ()
parserSpanDoesNotCreatePromotionReceipt : ParserSpanCreatesPromotionReceipt → ⊥
parserSpanDoesNotCreatePromotionReceipt ()
observationConsumerDoesNotCreateCanonicalTruth : ObservationConsumerCreatesCanonicalTruth → ⊥
observationConsumerDoesNotCreateCanonicalTruth ()
