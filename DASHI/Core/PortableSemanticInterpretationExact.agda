module DASHI.Core.PortableSemanticInterpretationExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- PORTABLE SEMANTIC INTERPRETATION
--
-- A backend may realise the same consumer-relevant meaning without sharing
-- syntax, execution order, algorithm, memory behaviour, performance, pixels,
-- or even a common implementation carrier with another backend.
--
-- Generic architecture and finite fixtures built on this surface are DASHI
-- synthesis.  Backend names used by child fixtures do not import the full
-- operational semantics of the named implementation technology.
------------------------------------------------------------------------

record SemanticInterpretationProblem : Set₁ where
  constructor semanticInterpretationProblem
  field
    Syntax : Set
    Meaning : Set
    Backend : Set
    Implementation : Backend → Set
    Query : Set
    Observation : Query → Set

    meaning : Syntax → Meaning
    observeMeaning : (query : Query) → Meaning → Observation query

    interpret :
      (backend : Backend) →
      Syntax →
      Implementation backend

    observeImplementation :
      (backend : Backend) →
      (query : Query) →
      Implementation backend →
      Observation query

open SemanticInterpretationProblem public

record SemanticRefinement
    (problem : SemanticInterpretationProblem)
    (backend : Backend problem)
    (syn : Syntax problem)
    (query : Query problem) : Set where
  constructor semanticRefinement
  field
    preservesObservation :
      observeImplementation problem backend query
        (interpret problem backend syn)
      ≡
      observeMeaning problem query (meaning problem syn)

open SemanticRefinement public

BackendEquivalentFor :
  (problem : SemanticInterpretationProblem) →
  Syntax problem →
  Query problem →
  Backend problem →
  Backend problem →
  Set
BackendEquivalentFor problem syn query left right =
  observeImplementation problem left query
      (interpret problem left syn)
  ≡
  observeImplementation problem right query
      (interpret problem right syn)

twoRefinementsGiveConsumerEquivalence :
  ∀ {problem syn query left right} →
  SemanticRefinement problem left syn query →
  SemanticRefinement problem right syn query →
  BackendEquivalentFor problem syn query left right
twoRefinementsGiveConsumerEquivalence leftReceipt rightReceipt =
  trans
    (preservesObservation leftReceipt)
    (sym (preservesObservation rightReceipt))

------------------------------------------------------------------------
-- Query-indexed equivalence is deliberately weaker than implementation
-- identity.  These are architectural non-implication receipts, not claims
-- about any particular concrete framework or runtime.
------------------------------------------------------------------------

record PortableSemanticInterpretationBoundary : Set where
  constructor portableSemanticInterpretationBoundary
  field
    sameConsumerSemanticsImpliesSameSyntax : Bool
    sameConsumerSemanticsImpliesSameSyntaxIsFalse :
      sameConsumerSemanticsImpliesSameSyntax ≡ false

    sameConsumerSemanticsImpliesSameAlgorithm : Bool
    sameConsumerSemanticsImpliesSameAlgorithmIsFalse :
      sameConsumerSemanticsImpliesSameAlgorithm ≡ false

    sameConsumerSemanticsImpliesSameExecutionOrder : Bool
    sameConsumerSemanticsImpliesSameExecutionOrderIsFalse :
      sameConsumerSemanticsImpliesSameExecutionOrder ≡ false

    sameConsumerSemanticsImpliesSamePerformance : Bool
    sameConsumerSemanticsImpliesSamePerformanceIsFalse :
      sameConsumerSemanticsImpliesSamePerformance ≡ false

    sameConsumerSemanticsImpliesSameMemoryBehaviour : Bool
    sameConsumerSemanticsImpliesSameMemoryBehaviourIsFalse :
      sameConsumerSemanticsImpliesSameMemoryBehaviour ≡ false

    sameConsumerSemanticsImpliesSamePixels : Bool
    sameConsumerSemanticsImpliesSamePixelsIsFalse :
      sameConsumerSemanticsImpliesSamePixels ≡ false

    backendEquivalenceIsConsumerIndexed : Bool
    backendEquivalenceIsConsumerIndexedIsTrue :
      backendEquivalenceIsConsumerIndexed ≡ true

open PortableSemanticInterpretationBoundary public

canonicalPortableSemanticInterpretationBoundary :
  PortableSemanticInterpretationBoundary
canonicalPortableSemanticInterpretationBoundary =
  portableSemanticInterpretationBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
