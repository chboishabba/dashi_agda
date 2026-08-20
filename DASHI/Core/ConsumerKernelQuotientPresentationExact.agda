module DASHI.Core.ConsumerKernelQuotientPresentationExact where

------------------------------------------------------------------------
-- CANONICAL CONSUMER-KERNEL QUOTIENT PRESENTATION
--
-- Top-down question:
--
--   what is the least observation needed by one declared deterministic
--   consumer F : State -> Outcome?
--
-- The exact equivalence relation is equality of consumer outcomes:
--
--   x ~F y  iff  F x = F y.
--
-- Agda does not provide quotient types definitionally, so this module follows
-- the repository's existing `FutureEquivalencePresentation` discipline:
-- a quotient is presented by a code map whose equality is sound AND complete
-- for the declared equivalence relation.  The consumer codomain itself gives
-- the canonical kernel presentation; no claim is made that unused Outcome
-- values are inhabited quotient classes.
--
-- SOURCE / METHOD CALIBRATION
--
-- David Blackwell, "Equivalent Comparisons of Experiments",
-- Annals of Mathematical Statistics 24(2), 1953, 265--272.
-- DOI: 10.1214/aoms/1177729032.
--
-- Patrick Cousot and Radhia Cousot,
-- "Abstract interpretation: a unified lattice model for static analysis of
-- programs by construction or approximation of fixpoints", POPL 1977.
-- DOI: 10.1145/512950.512973.
--
-- The constructive kernel quotient and factorization proofs below are local
-- DASHI results; the citations calibrate information-order terminology only.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.SectionedProjectionProvenanceBridgeExact as Sectioned

ConsumerEquivalent :
  ∀ {State Outcome : Set} ->
  (State -> Outcome) -> State -> State -> Set
ConsumerEquivalent consumer left right = consumer left ≡ consumer right

record ConsumerKernelPresentation
    {State Outcome : Set}
    (consumer : State -> Outcome) : Set₁ where
  constructor consumerKernelPresentation
  field
    QuotientCode : Set
    classOf : State -> QuotientCode
    classEqualitySound :
      ∀ {left right} ->
      classOf left ≡ classOf right ->
      ConsumerEquivalent consumer left right
    classEqualityComplete :
      ∀ {left right} ->
      ConsumerEquivalent consumer left right ->
      classOf left ≡ classOf right

open ConsumerKernelPresentation public

canonicalConsumerKernelPresentation :
  ∀ {State Outcome : Set}
    (consumer : State -> Outcome) ->
  ConsumerKernelPresentation consumer
canonicalConsumerKernelPresentation {Outcome = Outcome} consumer =
  consumerKernelPresentation
    Outcome
    consumer
    (λ same -> same)
    (λ same -> same)

canonicalClassIsConsumer :
  ∀ {State Outcome : Set}
    (consumer : State -> Outcome)
    (state : State) ->
  classOf (canonicalConsumerKernelPresentation consumer) state
  ≡ consumer state
canonicalClassIsConsumer consumer state = refl

canonicalKernelExactlyConsumerEquivalence :
  ∀ {State Outcome : Set}
    (consumer : State -> Outcome)
    {left right : State} ->
  classOf (canonicalConsumerKernelPresentation consumer) left
    ≡ classOf (canonicalConsumerKernelPresentation consumer) right ->
  consumer left ≡ consumer right
canonicalKernelExactlyConsumerEquivalence consumer same = same

canonicalConsumerQuotientIsSufficient :
  ∀ {State Outcome : Set}
    (consumer : State -> Outcome) ->
  Descent.ConsumerSufficient
    (classOf (canonicalConsumerKernelPresentation consumer))
    consumer
canonicalConsumerQuotientIsSufficient consumer left right same = same

record FactorizationThroughConsumerKernel
    {State Outcome Surface : Set}
    (consumer : State -> Outcome)
    (observe : State -> Surface)
    (presentation : ConsumerKernelPresentation consumer) : Set₁ where
  constructor factorizationThroughConsumerKernel
  field
    factor : Surface -> QuotientCode presentation
    factorizes :
      (state : State) ->
      classOf presentation state ≡ factor (observe state)

open FactorizationThroughConsumerKernel public

-- A sectioned observer sufficient for F cannot identify anything that the
-- canonical F-kernel keeps distinct.  Its surface therefore factors onto the
-- canonical quotient presentation.
sectionedSufficientObserverFactorsCanonical :
  ∀ {State Surface Outcome : Set}
    (projection : Sectioned.SectionedProjection State Surface)
    (consumer : State -> Outcome) ->
  Descent.ConsumerSufficient (Sectioned.project projection) consumer ->
  FactorizationThroughConsumerKernel
    consumer
    (Sectioned.project projection)
    (canonicalConsumerKernelPresentation consumer)
sectionedSufficientObserverFactorsCanonical projection consumer sufficient =
  factorizationThroughConsumerKernel
    (λ surface -> consumer (Sectioned.representative projection surface))
    (λ state ->
      sufficient
        state
        (Sectioned.representative projection (Sectioned.project projection state))
        (sym (Sectioned.section projection (Sectioned.project projection state))))

record ConsumerKernelQuotientBoundary : Set where
  constructor consumerKernelQuotientBoundary
  field
    kernelEqualityIsExactlyConsumerEquality : Bool
    canonicalConsumerPresentationIsSufficient : Bool
    everySectionedSufficientObserverFactorsCanonical : Bool
    unusedOutcomeValuesAreClaimedInhabitedClasses : Bool
    deterministicMinimalityMeansWorldCompleteness : Bool

canonicalConsumerKernelQuotientBoundary : ConsumerKernelQuotientBoundary
canonicalConsumerKernelQuotientBoundary =
  consumerKernelQuotientBoundary true true true false false
