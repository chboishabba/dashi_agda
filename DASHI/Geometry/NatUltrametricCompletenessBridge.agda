module DASHI.Geometry.NatUltrametricCompletenessBridge where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Ultrametric as UMetric
open import DASHI.Geometry.CompleteUltrametric as CU
open import DASHI.Geometry.CompleteUltrametricNat as CUN

data CompletenessLayer : Set where
  natDiscrete realCarrier surrealCarrier hilbertCarrier : CompletenessLayer

layerCompletenessSupported : CompletenessLayer → Bool
layerCompletenessSupported natDiscrete = true
layerCompletenessSupported realCarrier = false
layerCompletenessSupported surrealCarrier = false
layerCompletenessSupported hilbertCarrier = false

realCompletenessUnsupported :
  layerCompletenessSupported realCarrier ≡ false
realCompletenessUnsupported = refl

surrealCompletenessUnsupported :
  layerCompletenessSupported surrealCarrier ≡ false
surrealCompletenessUnsupported = refl

hilbertCompletenessUnsupported :
  layerCompletenessSupported hilbertCarrier ≡ false
hilbertCompletenessUnsupported = refl

record NatToNonNatCompletenessOrder
    {S : Set} (U : UMetric.Ultrametric S) : Set₁ where
  field
    sourceUltrametric : UMetric.Ultrametric S
    sourceUltrametricIsInput : sourceUltrametric ≡ U

    sourceCompletenessLayer : CompletenessLayer
    sourceCompletenessLayerIsNatDiscrete :
      sourceCompletenessLayer ≡ natDiscrete

    natCompletenessProof : CU.Complete sourceUltrametric
    natCompletenessProofIsCompleteNatUltrametric :
      natCompletenessProof ≡ CUN.completeNatUltrametric sourceUltrametric

    realPromotionPredecessor : CompletenessLayer
    realPromotionPredecessorIsNatDiscrete :
      realPromotionPredecessor ≡ natDiscrete
    realPromotionBlocker : Bool
    realPromotionBlockerIsFalse : realPromotionBlocker ≡ false

    surrealPromotionPredecessor : CompletenessLayer
    surrealPromotionPredecessorIsNatDiscrete :
      surrealPromotionPredecessor ≡ natDiscrete
    surrealPromotionBlocker : Bool
    surrealPromotionBlockerIsFalse : surrealPromotionBlocker ≡ false

    hilbertPromotionPredecessor : CompletenessLayer
    hilbertPromotionPredecessorIsNatDiscrete :
      hilbertPromotionPredecessor ≡ natDiscrete
    hilbertPromotionBlocker : Bool
    hilbertPromotionBlockerIsFalse : hilbertPromotionBlocker ≡ false

canonicalNatToNonNatCompletenessOrder :
  ∀ {S : Set} (U : UMetric.Ultrametric S) →
  NatToNonNatCompletenessOrder U
canonicalNatToNonNatCompletenessOrder U =
  record
    { sourceUltrametric = U
    ; sourceUltrametricIsInput = refl
    ; sourceCompletenessLayer = natDiscrete
    ; sourceCompletenessLayerIsNatDiscrete = refl
    ; natCompletenessProof = CUN.completeNatUltrametric U
    ; natCompletenessProofIsCompleteNatUltrametric = refl
    ; realPromotionPredecessor = natDiscrete
    ; realPromotionPredecessorIsNatDiscrete = refl
    ; realPromotionBlocker = false
    ; realPromotionBlockerIsFalse = refl
    ; surrealPromotionPredecessor = natDiscrete
    ; surrealPromotionPredecessorIsNatDiscrete = refl
    ; surrealPromotionBlocker = false
    ; surrealPromotionBlockerIsFalse = refl
    ; hilbertPromotionPredecessor = natDiscrete
    ; hilbertPromotionPredecessorIsNatDiscrete = refl
    ; hilbertPromotionBlocker = false
    ; hilbertPromotionBlockerIsFalse = refl
    }

record NatUltrametricCompletenessBridge
    {S : Set} (U : UMetric.Ultrametric S) : Set₁ where
  field
    dependencyOrder : NatToNonNatCompletenessOrder U

    discreteLayerComplete : CU.Complete U
    discreteLayerCompleteIsLoadBearing :
      discreteLayerComplete ≡ CUN.completeNatUltrametric U

    realCompletenessPromoted : Bool
    realCompletenessPromotedIsFalse : realCompletenessPromoted ≡ false

    surrealCompletenessPromoted : Bool
    surrealCompletenessPromotedIsFalse : surrealCompletenessPromoted ≡ false

    hilbertCompletenessPromoted : Bool
    hilbertCompletenessPromotedIsFalse : hilbertCompletenessPromoted ≡ false

canonicalNatUltrametricCompletenessBridge :
  ∀ {S : Set} (U : UMetric.Ultrametric S) →
  NatUltrametricCompletenessBridge U
canonicalNatUltrametricCompletenessBridge U =
  record
    { dependencyOrder = canonicalNatToNonNatCompletenessOrder U
    ; discreteLayerComplete = CUN.completeNatUltrametric U
    ; discreteLayerCompleteIsLoadBearing = refl
    ; realCompletenessPromoted = false
    ; realCompletenessPromotedIsFalse = refl
    ; surrealCompletenessPromoted = false
    ; surrealCompletenessPromotedIsFalse = refl
    ; hilbertCompletenessPromoted = false
    ; hilbertCompletenessPromotedIsFalse = refl
    }

natDiscreteCompleteness :
  ∀ {S : Set} (U : UMetric.Ultrametric S) → CU.Complete U
natDiscreteCompleteness U =
  NatUltrametricCompletenessBridge.discreteLayerComplete
    (canonicalNatUltrametricCompletenessBridge U)
