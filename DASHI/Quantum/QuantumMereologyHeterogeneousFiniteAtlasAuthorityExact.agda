{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumMereologyHeterogeneousFiniteAtlasAuthorityExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Quantum.QuantumMereologySourceAtlasExact as Sources

record HeterogeneousFiniteAtlasStatus : Set where
  field
    HeterogeneousCanonicalPairChartsSourceWritten : Bool
    HeterogeneousCanonicalPairChartsSourceWrittenIsTrue :
      HeterogeneousCanonicalPairChartsSourceWritten ≡ true

    ArbitraryFiniteSubsetMarginalsSourceWritten : Bool
    ArbitraryFiniteSubsetMarginalsSourceWrittenIsTrue :
      ArbitraryFiniteSubsetMarginalsSourceWritten ≡ true

    EveryMarginalUsesSameDeclaredGlobalState : Bool
    EveryMarginalUsesSameDeclaredGlobalStateIsTrue :
      EveryMarginalUsesSameDeclaredGlobalState ≡ true

    NestedMarginalCoherenceSourceWritten : Bool
    NestedMarginalCoherenceSourceWrittenIsFalse :
      NestedMarginalCoherenceSourceWritten ≡ false

    ArbitraryHilbertTPSCoordinateAttachmentPaid : Bool
    ArbitraryHilbertTPSCoordinateAttachmentPaidIsFalse :
      ArbitraryHilbertTPSCoordinateAttachmentPaid ≡ false

    ArbitraryGTPSCoordinateAttachmentPaid : Bool
    ArbitraryGTPSCoordinateAttachmentPaidIsFalse :
      ArbitraryGTPSCoordinateAttachmentPaid ≡ false

canonicalHeterogeneousFiniteAtlasStatus : HeterogeneousFiniteAtlasStatus
canonicalHeterogeneousFiniteAtlasStatus = record
  { HeterogeneousCanonicalPairChartsSourceWritten = true
  ; HeterogeneousCanonicalPairChartsSourceWrittenIsTrue = refl
  ; ArbitraryFiniteSubsetMarginalsSourceWritten = true
  ; ArbitraryFiniteSubsetMarginalsSourceWrittenIsTrue = refl
  ; EveryMarginalUsesSameDeclaredGlobalState = true
  ; EveryMarginalUsesSameDeclaredGlobalStateIsTrue = refl
  ; NestedMarginalCoherenceSourceWritten = false
  ; NestedMarginalCoherenceSourceWrittenIsFalse = refl
  ; ArbitraryHilbertTPSCoordinateAttachmentPaid = false
  ; ArbitraryHilbertTPSCoordinateAttachmentPaidIsFalse = refl
  ; ArbitraryGTPSCoordinateAttachmentPaid = false
  ; ArbitraryGTPSCoordinateAttachmentPaidIsFalse = refl
  }

leanHeterogeneousAtlasSourceReceipt : Sources.AttributionReceipt
leanHeterogeneousAtlasSourceReceipt =
  Sources.attribution-receipt
    Sources.importedFormalTheoremSource
    "DASHI Lean: QuantumMereologyHeterogeneousFiniteAtlas + QuantumMereologyFiniteSubsetMarginal"
    "Source-written Lean theorem surface constructing canonical pair/environment and arbitrary finite-subset/complement basis splits for heterogeneous dependent finite coordinate factors, then deriving pair/subset density matrices from one global density state. This is source authority only until exact-head Lean kernel evidence exists."

dashiHeterogeneousAtlasCrossModuleReceipt : Sources.AttributionReceipt
dashiHeterogeneousAtlasCrossModuleReceipt =
  Sources.attribution-receipt
    Sources.crossModuleInference
    "DASHI Agda"
    "Records the Lean finite-coordinate atlas theorem surface while keeping arbitrary Hilbert/g-TPS coordinate attachment and nested-subset marginal coherence explicitly unpaid."
