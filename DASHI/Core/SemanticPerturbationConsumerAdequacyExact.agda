module DASHI.Core.SemanticPerturbationConsumerAdequacyExact where

open import DASHI.Core.Prelude
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Core.QueryFactorisationSufficiency as Factor

------------------------------------------------------------------------
-- TYPED SEMANTIC PERTURBATION ADEQUACY
--
-- This is the query/consumer-relative crosswalk needed by the broader
-- geometric-reasoning / Sophontic-style intervention programme without
-- importing an unmerged sibling owner.  A perturbation states both the state
-- action and the expected action on the declared consumer answer.
------------------------------------------------------------------------

record ConsumerPerturbation
    {State Query : Set}
    (questions : Factor.InquiryQuestionFamily State Query)
    (query : Query) : Set₁ where
  constructor consumerPerturbation
  field
    actState : State → State
    actAnswer : Factor.Answer questions query → Factor.Answer questions query
    commutes :
      (state : State) →
      Factor.ask questions query (actState state)
      ≡ actAnswer (Factor.ask questions query state)

open ConsumerPerturbation public

SemanticPreserving :
  ∀ {State Query}
    {questions : Factor.InquiryQuestionFamily State Query}
    {query : Query} →
  ConsumerPerturbation questions query → Set
SemanticPreserving perturbation =
  (answer : Factor.Answer _ _) → actAnswer perturbation answer ≡ answer

semanticPreservingLeavesConsumerInvariant :
  ∀ {State Query}
    {questions : Factor.InquiryQuestionFamily State Query}
    {query : Query}
    (perturbation : ConsumerPerturbation questions query) →
  SemanticPreserving perturbation →
  (state : State) →
  Factor.ask questions query (actState perturbation state)
  ≡ Factor.ask questions query state
semanticPreservingLeavesConsumerInvariant perturbation preserving state =
  trans
    (commutes perturbation state)
    (preserving (Factor.ask _ _ state))

------------------------------------------------------------------------
-- Representation-level commuting square.
------------------------------------------------------------------------

record RepresentationPerturbationAdequacy
    {State Surface Query : Set}
    (questions : Factor.InquiryQuestionFamily State Query)
    (project : State → Surface)
    (query : Query)
    (perturbation : ConsumerPerturbation questions query) : Set₁ where
  constructor representationPerturbationAdequacy
  field
    factorisationReceipt : Factor.FactorsThrough questions project query
    actSurface : Surface → Surface
    representationCommutes :
      (state : State) →
      project (actState perturbation state)
      ≡ actSurface (project state)
    quotientCommutes :
      (surface : Surface) →
      Factor.quotientAnswer factorisationReceipt (actSurface surface)
      ≡ actAnswer perturbation
          (Factor.quotientAnswer factorisationReceipt surface)

open RepresentationPerturbationAdequacy public

representationSquareImpliesConsumerPerturbation :
  ∀ {State Surface Query}
    {questions : Factor.InquiryQuestionFamily State Query}
    {project : State → Surface}
    {query : Query}
    {perturbation : ConsumerPerturbation questions query} →
  RepresentationPerturbationAdequacy questions project query perturbation →
  (state : State) →
  Factor.ask questions query (actState perturbation state)
  ≡ actAnswer perturbation (Factor.ask questions query state)
representationSquareImpliesConsumerPerturbation witness state =
  trans
    (Factor.factorisation (factorisationReceipt witness)
      (actState _ state))
    (trans
      (cong
        (Factor.quotientAnswer (factorisationReceipt witness))
        (representationCommutes witness state))
      (trans
        (quotientCommutes witness (project state))
        (cong (actAnswer _)
          (sym (Factor.factorisation (factorisationReceipt witness) state)))))

record SemanticPerturbationBoundary : Set where
  constructor semanticPerturbationBoundary
  field
    semanticPreservingPerturbationMustPreserveDeclaredConsumer : Bool
    semanticChangingPerturbationCarriesExpectedAnswerAction : Bool
    representationMapAloneIsPerturbationAdequacy : Bool
    commutingSquarePlusFactorisationPaysPerturbationAdequacy : Bool

canonicalSemanticPerturbationBoundary : SemanticPerturbationBoundary
canonicalSemanticPerturbationBoundary =
  semanticPerturbationBoundary true true false true
