module DASHI.ComputerScience.ConsumerIndexedTernarySearchKernelExact where

open import DASHI.Core.Prelude
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

------------------------------------------------------------------------
-- GENERIC TERNARY DECISION × PROVENANCE
--
-- The trit is the consumer-relative decision surface.  Producer identity,
-- certification, scope and other explanation coordinates remain in provenance.
------------------------------------------------------------------------

record TernaryDecisionPacket (Provenance : Set) : Set where
  constructor ternaryDecisionPacket
  field
    decision : Trit
    provenance : Provenance

open TernaryDecisionPacket public

------------------------------------------------------------------------
-- CONSUMER-INDEXED TERNARY SEARCH KERNEL
--
-- This owner captures the generic finite-search semantics shared by theorem,
-- factor, model, and other bounded candidate searches.  It deliberately does
-- not own runtime halting semantics: bounded execution can resolve by terminal
-- machine state rather than by exhausting a finite candidate domain.
--
--   pos : at least one inspected candidate pays the declared Bool consumer
--   neg : no candidate pays, and a typed complete finite domain receipt exists
--   zer : no paying candidate found in the currently open/incomplete scope
--
-- A negative verdict is always relative to the declared admissible domain and
-- consumer.  It is not global impossibility without a separate lifting theorem.
------------------------------------------------------------------------

data _∈_ {A : Set} (x : A) : List A → Set where
  here : ∀ {xs} → x ∈ (x ∷ xs)
  there : ∀ {y xs} → x ∈ xs → x ∈ (y ∷ xs)

record CompleteFiniteSearchDomain (A : Set) : Set₁ where
  constructor completeFiniteSearchDomain
  field
    candidates : List A
    Admissible : A → Set
    coversEveryAdmissible :
      (candidate : A) → Admissible candidate → candidate ∈ candidates

open CompleteFiniteSearchDomain public

data SearchScope (A : Set) : Set₁ where
  openFiniteScope : List A → SearchScope A
  completeFiniteScope : CompleteFiniteSearchDomain A → SearchScope A

scopeCandidates : ∀ {A : Set} → SearchScope A → List A
scopeCandidates (openFiniteScope candidates) = candidates
scopeCandidates (completeFiniteScope domain) = candidates domain

anyPassing :
  ∀ {A : Set} →
  (A → Bool) →
  List A →
  Bool
anyPassing checker [] = false
anyPassing checker (candidate ∷ candidates) with checker candidate
... | true = true
... | false = anyPassing checker candidates

searchDecision :
  ∀ {A : Set} →
  (A → Bool) →
  SearchScope A →
  Trit
searchDecision checker scope with anyPassing checker (scopeCandidates scope)
... | true = pos
... | false with scope
...   | openFiniteScope _ = zer
...   | completeFiniteScope _ = neg

------------------------------------------------------------------------
-- Search provenance stays orthogonal to the ternary quotient.
------------------------------------------------------------------------

record SearchDecisionPacket (Candidate Provenance : Set) : Set₁ where
  constructor searchDecisionPacket
  field
    consumer : Candidate → Bool
    scope : SearchScope Candidate
    decision : Trit
    decisionExact : decision ≡ searchDecision consumer scope
    provenance : Provenance

open SearchDecisionPacket public

forgetSearchMechanism :
  ∀ {Candidate Provenance} →
  SearchDecisionPacket Candidate Provenance →
  TernaryDecisionPacket Provenance
forgetSearchMechanism packet =
  ternaryDecisionPacket (SearchDecisionPacket.decision packet) (SearchDecisionPacket.provenance packet)

------------------------------------------------------------------------
-- Information refinement order used by bounded search and other monotone
-- ternary decision producers.
------------------------------------------------------------------------

data SearchDecisionRefines : Trit → Trit → Set where
  unresolvedStaysUnresolved : SearchDecisionRefines zer zer
  unresolvedBecomesNegative : SearchDecisionRefines zer neg
  unresolvedBecomesPositive : SearchDecisionRefines zer pos
  negativeStaysNegative : SearchDecisionRefines neg neg
  positiveStaysPositive : SearchDecisionRefines pos pos

data ResolvedSearchFlipsSign : Set where
data ResolvedSearchReturnsUnresolved : Set where

resolvedSearchDoesNotFlipSign : ResolvedSearchFlipsSign → ⊥
resolvedSearchDoesNotFlipSign ()

resolvedSearchDoesNotReturnUnresolved : ResolvedSearchReturnsUnresolved → ⊥
resolvedSearchDoesNotReturnUnresolved ()

------------------------------------------------------------------------
-- Binary quotient obstruction.
------------------------------------------------------------------------

legacyFoundBit : Trit → Bool
legacyFoundBit neg = false
legacyFoundBit zer = false
legacyFoundBit pos = true

legacyFoundBitConflatesExhaustedAndOpen : legacyFoundBit neg ≡ legacyFoundBit zer
legacyFoundBitConflatesExhaustedAndOpen = refl

-- Same negative value can have different domain/provenance semantics; the trit
-- alone therefore cannot identify why the search is negative.
data NegativeTritDeterminesScopeOrProvenance : Set where

negativeTritDoesNotDetermineScopeOrProvenance :
  NegativeTritDeterminesScopeOrProvenance → ⊥
negativeTritDoesNotDetermineScopeOrProvenance ()

-- Scoped finite exhaustion is not automatically global impossibility.
data ScopedNegativeMeansGlobalImpossibility : Set where

scopedNegativeDoesNotMeanGlobalImpossibility :
  ScopedNegativeMeansGlobalImpossibility → ⊥
scopedNegativeDoesNotMeanGlobalImpossibility ()

record ConsumerIndexedTernarySearchBoundary : Set where
  constructor consumerIndexedTernarySearchBoundary
  field
    genericDecisionProvenanceProduct : Bool
    consumerIndexed : Bool
    openFailureRemainsUnresolved : Bool
    negativeRequiresTypedFiniteCoverage : Bool
    positiveRequiresPayingCandidate : Bool
    provenanceSeparateFromDecision : Bool
    binaryFoundBitConflatesNegativeAndUnresolved : Bool
    scopedNegativeIsGlobalImpossibility : Bool
    runtimeHaltingCollapsedIntoFiniteEnumeration : Bool

canonicalConsumerIndexedTernarySearchBoundary :
  ConsumerIndexedTernarySearchBoundary
canonicalConsumerIndexedTernarySearchBoundary =
  consumerIndexedTernarySearchBoundary
    true true true true true true true false false
