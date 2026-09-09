module DASHI.Core.ConsumerFibreRepairExact where

open import DASHI.Core.Prelude

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.ObserverRefinementLatticeExact as Observer

------------------------------------------------------------------------
-- CONSUMER-RELATIVE FIBRE REPAIR
--
-- A coarse observer collision that changes a declared consumer is not merely
-- evidence that the observer is "missing information" in the abstract.  It is
-- a typed obstruction to ConsumerSufficient / FactorsThrough for that exact
-- consumer.  Any refinement that genuinely repairs sufficiency must separate
-- the witnessed colliding states.
--
-- IMPORTANT REUSE: observer pairing is not redefined here.  Refinements use
-- the canonical ObserverRefinementLatticeExact.pairObserver.
--
-- The theorem is intentionally one-way: a separating coordinate is necessary
-- for repairing this witnessed collision, but separation alone does not prove
-- global ConsumerSufficient.  This preserves the repo's non-promotion
-- discipline and makes the result suitable for instrumentation, source/build
-- provenance, supply-chain, and experiment-design consumers.
------------------------------------------------------------------------

RefinementRepairs :
  ∀ {State Surface Refinement Outcome : Set} →
  (State → Surface) →
  (State → Refinement) →
  (State → Outcome) →
  Set
RefinementRepairs observe refine consumer =
  Descent.ConsumerSufficient
    (Observer.pairObserver observe refine)
    consumer

refinementRepairSeparatesWitness :
  ∀ {State Surface Refinement Outcome : Set}
    {observe : State → Surface}
    {refine : State → Refinement}
    {consumer : State → Outcome} →
  (witness : Descent.ConsumerNonDescentWitness observe consumer) →
  RefinementRepairs observe refine consumer →
  refine (Descent.left witness) ≡ refine (Descent.right witness) →
  ⊥
refinementRepairSeparatesWitness witness repaired sameRefinement =
  Descent.differentOutcome witness
    (repaired
      (Descent.left witness)
      (Descent.right witness)
      (cong₂ _,_
        (Descent.sameSurface witness)
        sameRefinement))

factorizationRepairSeparatesWitness :
  ∀ {State Surface Refinement Outcome : Set}
    {observe : State → Surface}
    {refine : State → Refinement}
    {consumer : State → Outcome} →
  (witness : Descent.ConsumerNonDescentWitness observe consumer) →
  Descent.FactorsThrough
    (Observer.pairObserver observe refine)
    consumer →
  refine (Descent.left witness) ≡ refine (Descent.right witness) →
  ⊥
factorizationRepairSeparatesWitness witness factors sameRefinement =
  refinementRepairSeparatesWitness witness
    (Descent.fibreConstantIsConsumerSufficient
      (Descent.factorsThroughImpliesFibreConstant factors))
    sameRefinement

record ConsumerFibreRepairBoundary : Set where
  constructor consumerFibreRepairBoundary
  field
    collisionForcesSeparationInEverySufficientRepair : Bool
    separatingOneWitnessAloneProvesGlobalSufficiency : Bool
    repairIsConsumerIndexed : Bool
    observerPairingHasSingleCanonicalOwner : Bool

canonicalConsumerFibreRepairBoundary : ConsumerFibreRepairBoundary
canonicalConsumerFibreRepairBoundary =
  consumerFibreRepairBoundary true false true true
