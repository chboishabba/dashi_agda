module DASHI.Programmes.CoreExecutableParityReceiptExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- dashiCORE executable parity boundary.
--
-- The satellite itself documents StateFingerprint as a deterministic backend
-- parity witness and explicitly excludes it from semantic/kernel/defect/MDL
-- logic.  The formal consumer therefore asks for reference commutation, not
-- merely a matching UInt64 observation.
------------------------------------------------------------------------

record CoreReferenceExecutionReceipt : Set₁ where
  constructor core-reference-execution-receipt
  field
    State Operation ReferenceBackend CandidateBackend Observation : Set

    referenceRun : Operation → State → State
    candidateRun : Operation → State → State
    observe : State → Observation

    -- Cheap regression witness; useful but insufficient by itself.
    observationParity :
      (op : Operation) → (state : State) →
      observe (referenceRun op state) ≡ observe (candidateRun op state)

    -- The theorem-facing semantic bridge.  The concrete relation may be exact
    -- state equality or another formally justified observational/refinement
    -- relation supplied by the consumer.
    SemanticallyEquivalent : State → State → Set
    semanticCommutation :
      (op : Operation) → (state : State) →
      SemanticallyEquivalent
        (referenceRun op state)
        (candidateRun op state)

open CoreReferenceExecutionReceipt public

record CoreExecutableParityBoundary : Set where
  constructor core-executable-parity-boundary
  field
    matchingFingerprintIsSemanticEquality : Bool
    matchingFingerprintIsSemanticEqualityIsFalse :
      matchingFingerprintIsSemanticEquality ≡ false

    gpuSlowerThanCpuIsCorrectnessFailure : Bool
    gpuSlowerThanCpuIsCorrectnessFailureIsFalse :
      gpuSlowerThanCpuIsCorrectnessFailure ≡ false

    runtimeFailureIsFormalCounterexampleByItself : Bool
    runtimeFailureIsFormalCounterexampleByItselfIsFalse :
      runtimeFailureIsFormalCounterexampleByItself ≡ false

    referenceCommutationCanCarryFormalClaims : Bool
    referenceCommutationCanCarryFormalClaimsIsTrue :
      referenceCommutationCanCarryFormalClaims ≡ true

canonicalCoreExecutableParityBoundary : CoreExecutableParityBoundary
canonicalCoreExecutableParityBoundary =
  core-executable-parity-boundary
    false refl
    false refl
    false refl
    true refl
