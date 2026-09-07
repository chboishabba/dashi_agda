{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanPath13Eq119T3MinimalScalarProvenanceExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record T3MinimalScalarSourceStatus : Set where
  constructor t3MinimalScalarSourceStatus
  field
    bishopBridgeCompatibilityProducerClosed : Bool
    preferredRouteRequiresWholeBishopBridge : Bool
    preferredRouteRequiresRationalRealRingEmbedding : Bool
    preferredRouteRequiresSelectedVariationalRepresentation : Bool
    preferredRouteRequiresSelectedNormalizedT3Data : Bool
    preferredRouteRequiresCutThreshold : Bool
    physicalEq119Closed : Bool
open T3MinimalScalarSourceStatus public

canonicalT3MinimalScalarSourceStatus : T3MinimalScalarSourceStatus
canonicalT3MinimalScalarSourceStatus =
  t3MinimalScalarSourceStatus true false true true true true false

bishopCompatibilityClosedIsTrue :
  bishopBridgeCompatibilityProducerClosed canonicalT3MinimalScalarSourceStatus ≡ true
bishopCompatibilityClosedIsTrue = refl

wholeBishopBridgeNoLongerRequired :
  preferredRouteRequiresWholeBishopBridge canonicalT3MinimalScalarSourceStatus ≡ false
wholeBishopBridgeNoLongerRequired = refl

rationalRealRingEmbeddingStillRequired :
  preferredRouteRequiresRationalRealRingEmbedding canonicalT3MinimalScalarSourceStatus ≡ true
rationalRealRingEmbeddingStillRequired = refl

physicalEq119StillOpen :
  physicalEq119Closed canonicalT3MinimalScalarSourceStatus ≡ false
physicalEq119StillOpen = refl

cmp98Path13T3MinimalScalarProvenanceLevel : ProofLevel
cmp98Path13T3MinimalScalarProvenanceLevel = machineChecked
