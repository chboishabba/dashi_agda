{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanPath13Eq119BishopBridgeProvenanceExact where

------------------------------------------------------------------------
-- PATH13 EQ. (119): SCALAR-TRANSPORT OWNERSHIP SUPERSESSION
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanR208BishopLegacyRingEmbeddingExact as Scalar
import DASHI.Physics.YangMills.BalabanCMP98Path13BishopBridgeSourceFamilyExact as Source

record Path13BishopBridgeSourceStatus : Set where
  field
    bishopToR208RingEmbeddingCompilerClosed : Bool
    bishopBridgePath13SourceAdapterClosed : Bool
    bespokeR208RingEmbeddingPaymentRequired : Bool

    bishopToLegacyRealBridgeConstructed : Bool
    selectedVariationalOperatorRepresentationConstructed : Bool
    federbushConventionFamilyConstructed : Bool
    selectedCutThresholdConstructed : Bool
    physicalEq119Closed : Bool

    bishopToR208RingEmbeddingCompilerClosedIsTrue :
      bishopToR208RingEmbeddingCompilerClosed ≡ true
    bishopBridgePath13SourceAdapterClosedIsTrue :
      bishopBridgePath13SourceAdapterClosed ≡ true
    bespokeR208RingEmbeddingPaymentRequiredIsFalse :
      bespokeR208RingEmbeddingPaymentRequired ≡ false

    bishopToLegacyRealBridgeConstructedIsFalse :
      bishopToLegacyRealBridgeConstructed ≡ false
    selectedVariationalOperatorRepresentationConstructedIsFalse :
      selectedVariationalOperatorRepresentationConstructed ≡ false
    federbushConventionFamilyConstructedIsFalse :
      federbushConventionFamilyConstructed ≡ false
    selectedCutThresholdConstructedIsFalse :
      selectedCutThresholdConstructed ≡ false
    physicalEq119ClosedIsFalse : physicalEq119Closed ≡ false

open Path13BishopBridgeSourceStatus public

canonicalPath13BishopBridgeSourceStatus : Path13BishopBridgeSourceStatus
canonicalPath13BishopBridgeSourceStatus = record
  { bishopToR208RingEmbeddingCompilerClosed = true
  ; bishopBridgePath13SourceAdapterClosed = true
  ; bespokeR208RingEmbeddingPaymentRequired = false
  ; bishopToLegacyRealBridgeConstructed = false
  ; selectedVariationalOperatorRepresentationConstructed = false
  ; federbushConventionFamilyConstructed = false
  ; selectedCutThresholdConstructed = false
  ; physicalEq119Closed = false
  ; bishopToR208RingEmbeddingCompilerClosedIsTrue = refl
  ; bishopBridgePath13SourceAdapterClosedIsTrue = refl
  ; bespokeR208RingEmbeddingPaymentRequiredIsFalse = refl
  ; bishopToLegacyRealBridgeConstructedIsFalse = refl
  ; selectedVariationalOperatorRepresentationConstructedIsFalse = refl
  ; federbushConventionFamilyConstructedIsFalse = refl
  ; selectedCutThresholdConstructedIsFalse = refl
  ; physicalEq119ClosedIsFalse = refl
  }

bespokeR208PaymentPruned :
  bespokeR208RingEmbeddingPaymentRequired
    canonicalPath13BishopBridgeSourceStatus ≡ false
bespokeR208PaymentPruned = refl

foundationalBridgeStillOpen :
  bishopToLegacyRealBridgeConstructed
    canonicalPath13BishopBridgeSourceStatus ≡ false
foundationalBridgeStillOpen = refl

bishopR208CompilerLevel : ProofLevel
bishopR208CompilerLevel = Scalar.r208BishopLegacyRingEmbeddingCompilerLevel

bishopBridgeSourceAdapterLevel : ProofLevel
bishopBridgeSourceAdapterLevel = Source.cmp98Path13BishopBridgeSourceAdapterLevel

cmp98Path13BishopBridgeProvenanceLevel : ProofLevel
cmp98Path13BishopBridgeProvenanceLevel = machineChecked
