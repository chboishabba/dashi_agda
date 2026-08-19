module DASHI.Core.ConsumerQuotientBaseChangeExact where

------------------------------------------------------------------------
-- CONTEXT / BASE CHANGE FOR CANONICAL CONSUMER QUOTIENTS
--
-- Given a fine restriction
--
--   restrict : FineD -> FineC
--
-- and context-local consumers
--
--   consumerD : FineD -> OutcomeD
--   consumerC : FineC -> OutcomeC,
--
-- the consumer-minimal quotient transports exactly when the coarse target
-- outcome after restriction depends only on the source consumer class:
--
--   consumerD x = consumerD y
--     -> consumerC (restrict x) = consumerC (restrict y).
--
-- With a section of consumerD this fibre-constancy condition constructs the
-- induced base-change map
--
--   OutcomeD -> OutcomeC
--
-- and the commuting square.  Induced maps compose and have identities.
--
-- SOURCE / METHOD CALIBRATION
--
-- Jean Benabou, "Fibered Categories and the Foundations of Naive Category
-- Theory", Journal of Symbolic Logic 50(1), 1985, 10--37.
-- DOI: 10.2307/2273784.
--
-- Saunders Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
-- Springer, 1998. DOI: 10.1007/978-1-4757-4721-8.
--
-- The local theorem is only a strict consumer-quotient base-change result.  It
-- does not assert full cartesian uniqueness or Grothendieck equivalence.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ContextIndexedObservationFibrationExact as Context
import DASHI.Core.SectionedProjectionProvenanceBridgeExact as Sectioned
import DASHI.Core.ProjectionCategory as Cat

ConsumerFibreCompatibility :
  ∀ {FineD FineC OutcomeD OutcomeC : Set} ->
  (FineD -> FineC) ->
  (FineD -> OutcomeD) ->
  (FineC -> OutcomeC) ->
  Set
ConsumerFibreCompatibility restrict consumerD consumerC =
  ∀ left right ->
  consumerD left ≡ consumerD right ->
  consumerC (restrict left) ≡ consumerC (restrict right)

record ConsumerBaseChange
    {FineD FineC OutcomeD OutcomeC : Set}
    (restrict : FineD -> FineC)
    (consumerD : FineD -> OutcomeD)
    (consumerC : FineC -> OutcomeC) : Set₁ where
  constructor consumerBaseChange
  field
    transportOutcome : OutcomeD -> OutcomeC
    commutes :
      (state : FineD) ->
      consumerC (restrict state)
      ≡ transportOutcome (consumerD state)

open ConsumerBaseChange public

baseChangeImpliesFibreCompatibility :
  ∀ {FineD FineC OutcomeD OutcomeC : Set}
    {restrict : FineD -> FineC}
    {consumerD : FineD -> OutcomeD}
    {consumerC : FineC -> OutcomeC} ->
  ConsumerBaseChange restrict consumerD consumerC ->
  ConsumerFibreCompatibility restrict consumerD consumerC
baseChangeImpliesFibreCompatibility change left right same =
  trans
    (commutes change left)
    (trans
      (cong (transportOutcome change) same)
      (sym (commutes change right)))

sectionedCompatibilityConstructsBaseChange :
  ∀ {FineD FineC OutcomeD OutcomeC : Set}
    (restrict : FineD -> FineC)
    (consumerC : FineC -> OutcomeC)
    (sectioned : Sectioned.SectionedProjection FineD OutcomeD) ->
  ConsumerFibreCompatibility
    restrict
    (Sectioned.project sectioned)
    consumerC ->
  ConsumerBaseChange
    restrict
    (Sectioned.project sectioned)
    consumerC
sectionedCompatibilityConstructsBaseChange
  restrict consumerC sectioned compatible =
  consumerBaseChange
    (λ outcome ->
      consumerC (restrict (Sectioned.representative sectioned outcome)))
    (λ state ->
      compatible
        state
        (Sectioned.representative sectioned (Sectioned.project sectioned state))
        (sym (Sectioned.section sectioned (Sectioned.project sectioned state))))

identityConsumerBaseChange :
  ∀ {Fine Outcome : Set}
    (consumer : Fine -> Outcome) ->
  ConsumerBaseChange (λ x -> x) consumer consumer
identityConsumerBaseChange consumer =
  consumerBaseChange (λ x -> x) (λ state -> refl)

composeConsumerBaseChange :
  ∀ {FineA FineB FineC OutcomeA OutcomeB OutcomeC : Set}
    {restrictBA : FineB -> FineA}
    {restrictCB : FineC -> FineB}
    {consumerA : FineA -> OutcomeA}
    {consumerB : FineB -> OutcomeB}
    {consumerC : FineC -> OutcomeC} ->
  ConsumerBaseChange restrictBA consumerB consumerA ->
  ConsumerBaseChange restrictCB consumerC consumerB ->
  ConsumerBaseChange
    (λ state -> restrictBA (restrictCB state))
    consumerC
    consumerA
composeConsumerBaseChange first second =
  consumerBaseChange
    (λ outcome -> transportOutcome first (transportOutcome second outcome))
    (λ state ->
      trans
        (commutes first (restrictCB state))
        (cong (transportOutcome first) (commutes second state)))

------------------------------------------------------------------------
-- Direct specialization to the context-indexed observation carrier.
------------------------------------------------------------------------

record ContextConsumerSection
    {base : Cat.ProjectionCategory}
    {indexed : Context.ContextIndexedObservation base}
    (consumer : Context.ContextConsumer indexed)
    (context : Cat.Obj base) : Set₁ where
  constructor contextConsumerSection
  field
    representativeOutcome :
      Context.Outcome consumer context -> Context.Fine indexed context
    sectionOutcome :
      (outcome : Context.Outcome consumer context) ->
      Context.consume consumer context (representativeOutcome outcome) ≡ outcome

open ContextConsumerSection public

contextConsumerSectioned :
  ∀ {base : Cat.ProjectionCategory}
    {indexed : Context.ContextIndexedObservation base}
    {consumer : Context.ContextConsumer indexed}
    {context : Cat.Obj base} ->
  ContextConsumerSection consumer context ->
  Sectioned.SectionedProjection
    (Context.Fine indexed context)
    (Context.Outcome consumer context)
contextConsumerSectioned {consumer = consumer} {context = context} section =
  Sectioned.sectionedProjection
    (Context.consume consumer context)
    (representativeOutcome section)
    (sectionOutcome section)

ContextConsumerCompatibility :
  ∀ {base : Cat.ProjectionCategory}
    {indexed : Context.ContextIndexedObservation base} ->
  Context.ContextConsumer indexed ->
  ∀ {A B : Cat.Obj base} ->
  Cat.Hom base A B ->
  Set
ContextConsumerCompatibility {indexed = indexed} consumer {A} {B} change =
  ConsumerFibreCompatibility
    (Context.restrictFine indexed change)
    (Context.consume consumer B)
    (Context.consume consumer A)

contextCompatibilityConstructsConsumerBaseChange :
  ∀ {base : Cat.ProjectionCategory}
    {indexed : Context.ContextIndexedObservation base}
    (consumer : Context.ContextConsumer indexed)
    {A B : Cat.Obj base}
    (change : Cat.Hom base A B) ->
  ContextConsumerSection consumer B ->
  ContextConsumerCompatibility consumer change ->
  ConsumerBaseChange
    (Context.restrictFine indexed change)
    (Context.consume consumer B)
    (Context.consume consumer A)
contextCompatibilityConstructsConsumerBaseChange
  {indexed = indexed} consumer {A} {B} change section compatible =
  sectionedCompatibilityConstructsBaseChange
    (Context.restrictFine indexed change)
    (Context.consume consumer A)
    (contextConsumerSectioned section)
    compatible

record ConsumerQuotientBaseChangeBoundary : Set where
  constructor consumerQuotientBaseChangeBoundary
  field
    fibreCompatibilityIsNecessary : Bool
    sectionedFibreCompatibilityConstructsTransport : Bool
    inducedTransportHasIdentity : Bool
    inducedTransportsCompose : Bool
    contextLocalAdequacyAutomaticallyImpliesBaseChange : Bool
    baseChangeMeansWorldSemanticIdentity : Bool

canonicalConsumerQuotientBaseChangeBoundary :
  ConsumerQuotientBaseChangeBoundary
canonicalConsumerQuotientBaseChangeBoundary =
  consumerQuotientBaseChangeBoundary true true true true false false
