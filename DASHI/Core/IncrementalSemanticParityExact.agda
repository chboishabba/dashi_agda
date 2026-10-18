module DASHI.Core.IncrementalSemanticParityExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- DIRECT / REFERENCE PARITY
--
-- Incremental semantic reconstruction is an optimisation. A sampled full
-- rebuild is the reference path. A mismatch is a typed validation failure,
-- never permission to keep rendering the divergent fast path.
------------------------------------------------------------------------

data SemanticParityResult : Set where
  semanticParityPass : SemanticParityResult
  semanticParityFail : SemanticParityResult

data ParityDisposition : Set where
  continueIncrementalHistory : ParityDisposition
  stopOnSemanticDivergence : ParityDisposition

parityDisposition :
  SemanticParityResult →
  ParityDisposition
parityDisposition semanticParityPass =
  continueIncrementalHistory
parityDisposition semanticParityFail =
  stopOnSemanticDivergence

parityFailureStops :
  parityDisposition semanticParityFail
    ≡ stopOnSemanticDivergence
parityFailureStops = refl

record IncrementalParityBoundary : Set where
  constructor incrementalParityBoundary
  field
    parityFailureMayBeIgnored : Bool
    parityFailureMayBeIgnoredIsFalse :
      parityFailureMayBeIgnored ≡ false

    referenceRebuildMayUseDifferentSemanticRules : Bool
    referenceRebuildMayUseDifferentSemanticRulesIsFalse :
      referenceRebuildMayUseDifferentSemanticRules ≡ false

    paritySamplingMayGrantSemanticAuthority : Bool
    paritySamplingMayGrantSemanticAuthorityIsFalse :
      paritySamplingMayGrantSemanticAuthority ≡ false

canonicalIncrementalParityBoundary :
  IncrementalParityBoundary
canonicalIncrementalParityBoundary =
  incrementalParityBoundary
    false refl
    false refl
    false refl
