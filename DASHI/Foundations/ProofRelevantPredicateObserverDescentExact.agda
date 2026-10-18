module DASHI.Foundations.ProofRelevantPredicateObserverDescentExact where

------------------------------------------------------------------------
-- PROOF-RELEVANT PREDICATE DESCENT THROUGH AN OBSERVER
--
-- DASHI CONTRIBUTION
--
-- PredicatePullbackLatticeExact owns the Bool-valued predicate lattice.  Some
-- theorem-facing consumers, including the literal RH critical-line predicate,
-- are proof-relevant Set-valued predicates.  This owner supplies only the
-- corresponding descent interface:
--
--   Fine --observe--> Coarse
--    |                 |
--    P              coarseP
--
-- with theorem-bearing forward/backward maps at each fine point.
--
-- It is a frontend over ObserverWithFibre, not a replacement for the existing
-- Bool predicate lattice or the Set-valued consumer-descent spine.
------------------------------------------------------------------------

open import Agda.Primitive using (Set; Set₁)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Foundations.HyperformChartGluingExact as Glue

record PredicateFactorsThroughObserver
    {Fine Coarse : Set}
    (observer : Glue.ObserverWithFibre Fine Coarse)
    (predicate : Fine → Set) : Set₁ where
  field
    coarsePredicate : Coarse → Set

    forward :
      (fine : Fine) →
      predicate fine →
      coarsePredicate (Glue.observe observer fine)

    backward :
      (fine : Fine) →
      coarsePredicate (Glue.observe observer fine) →
      predicate fine

open PredicateFactorsThroughObserver public

predicateTransportAcrossObserverFibre :
  ∀ {Fine Coarse : Set}
    {observer : Glue.ObserverWithFibre Fine Coarse}
    {predicate : Fine → Set} →
  PredicateFactorsThroughObserver observer predicate →
  (left right : Fine) →
  Glue.observe observer left ≡ Glue.observe observer right →
  predicate left →
  predicate right
predicateTransportAcrossObserverFibre factors left right same observed =
  backward factors right
    (subst
      (coarsePredicate factors)
      same
      (forward factors left observed))

predicateIsObserverFibreConstant :
  ∀ {Fine Coarse : Set}
    {observer : Glue.ObserverWithFibre Fine Coarse}
    {predicate : Fine → Set} →
  PredicateFactorsThroughObserver observer predicate →
  (left right : Fine) →
  Glue.observe observer left ≡ Glue.observe observer right →
  predicate left →
  predicate right
predicateIsObserverFibreConstant =
  predicateTransportAcrossObserverFibre

record ProofRelevantPredicateObserverBoundary : Set where
  constructor proof-relevant-predicate-observer-boundary
  field
    boolPredicateLatticeReplaced : Bool
    proofRelevantPredicateDescentOwned : Bool
    forwardBackwardWitnessesRequired : Bool
    equalObservationTransportsPredicateEvidence : Bool
    descentManufacturesPredicateTruth : Bool

open ProofRelevantPredicateObserverBoundary public

canonicalProofRelevantPredicateObserverBoundary :
  ProofRelevantPredicateObserverBoundary
canonicalProofRelevantPredicateObserverBoundary =
  proof-relevant-predicate-observer-boundary
    false true true true false
