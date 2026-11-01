module DASHI.Foundations.HyperformObserverFactorisationExact where

------------------------------------------------------------------------
-- OBSERVER FIBRES AS CONSUMER-INDEXED FACTORISATION / NON-FACTORABILITY
--
-- DASHI CONTRIBUTION
--
-- HyperformChartGluingExact distinguishes a fine carrier from a coarse
-- observation and retains the observer fibre explicitly.  This module connects
-- that geometry to the repository's canonical consumer-adequacy calculus:
--
--   consumer is safe on the coarse observer
--     iff a FactorsThrough witness is supplied.
--
-- A collision in one observer fibre that the consumer distinguishes is a
-- NonFactorabilityWitness.  Any downstream relabelling, pants coordinate,
-- rendering, codec, or other post-composition of the same coarse observer
-- inherits that obstruction: postprocessing cannot recreate erased data.
--
-- This is generic mathematics.  It does not claim that every coarse observer
-- is inadequate; adequacy is consumer-indexed and proof-relevant.
------------------------------------------------------------------------

open import Agda.Primitive using (Set; Set₁)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (cong)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.ConsumerFibreRepairExact as Repair
import DASHI.Core.FactorisationSpineCrosswalkExact as Spine
import DASHI.Foundations.HyperformChartGluingExact as Glue

ObserverConsumerAdequate :
  ∀ {Fine Coarse Outcome : Set} →
  Glue.ObserverWithFibre Fine Coarse →
  (Fine → Outcome) →
  Set₁
ObserverConsumerAdequate observer consumer =
  Descent.FactorsThrough (Glue.observe observer) consumer

ObserverConsumerSufficient :
  ∀ {Fine Coarse Outcome : Set} →
  Glue.ObserverWithFibre Fine Coarse →
  (Fine → Outcome) →
  Set
ObserverConsumerSufficient observer consumer =
  Descent.ConsumerSufficient (Glue.observe observer) consumer

record ObserverFibreDistinction
    {Fine Coarse Outcome : Set}
    (observer : Glue.ObserverWithFibre Fine Coarse)
    (consumer : Fine → Outcome) : Set₁ where
  constructor observer-fibre-distinction
  field
    left right : Fine
    sameObservation :
      Glue.observe observer left
      ≡ Glue.observe observer right
    consumerDistinguishes :
      consumer left ≡ consumer right → ⊥

open ObserverFibreDistinction public

asConsumerNonDescentWitness :
  ∀ {Fine Coarse Outcome}
    {observer : Glue.ObserverWithFibre Fine Coarse}
    {consumer : Fine → Outcome} →
  ObserverFibreDistinction observer consumer →
  Descent.ConsumerNonDescentWitness
    (Glue.observe observer)
    consumer
asConsumerNonDescentWitness witness =
  Descent.consumerNonDescentWitness
    (left witness)
    (right witness)
    (sameObservation witness)
    (consumerDistinguishes witness)

asNonFactorabilityWitness :
  ∀ {Fine Coarse Outcome}
    {observer : Glue.ObserverWithFibre Fine Coarse}
    {consumer : Fine → Outcome} →
  ObserverFibreDistinction observer consumer →
  INF.NonFactorabilityWitness
    (Glue.observe observer)
    consumer
asNonFactorabilityWitness witness =
  Spine.nonDescentToNonFactorability
    (asConsumerNonDescentWitness witness)

nonFactorableObserverIsNotConsumerAdequate :
  ∀ {Fine Coarse Outcome}
    {observer : Glue.ObserverWithFibre Fine Coarse}
    {consumer : Fine → Outcome} →
  ObserverFibreDistinction observer consumer →
  ObserverConsumerAdequate observer consumer →
  ⊥
nonFactorableObserverIsNotConsumerAdequate witness =
  Descent.nonDescentWitnessBlocksFactorization
    (asConsumerNonDescentWitness witness)

nonFactorableObserverIsNotConsumerSufficient :
  ∀ {Fine Coarse Outcome}
    {observer : Glue.ObserverWithFibre Fine Coarse}
    {consumer : Fine → Outcome} →
  ObserverFibreDistinction observer consumer →
  ObserverConsumerSufficient observer consumer →
  ⊥
nonFactorableObserverIsNotConsumerSufficient witness =
  Descent.nonDescentWitnessBlocksSufficiency
    (asConsumerNonDescentWitness witness)

observerRepairRequiresWitnessSeparation :
  ∀ {Fine Coarse Refinement Outcome}
    {observer : Glue.ObserverWithFibre Fine Coarse}
    {refine : Fine → Refinement}
    {consumer : Fine → Outcome} →
  (witness : ObserverFibreDistinction observer consumer) →
  Repair.RefinementRepairs
    (Glue.observe observer)
    refine
    consumer →
  refine (left witness) ≡ refine (right witness) →
  ⊥
observerRepairRequiresWitnessSeparation witness =
  Repair.refinementRepairSeparatesWitness
    (asConsumerNonDescentWitness witness)

rechartObserver :
  ∀ {Fine Coarse Recharted} →
  Glue.ObserverWithFibre Fine Coarse →
  (Coarse → Recharted) →
  Glue.ObserverWithFibre Fine Recharted
rechartObserver observer rechart = record
  { Glue.observe = λ fine →
      rechart (Glue.observe observer fine)
  }

rechartCannotRecoverObserverFibreDistinction :
  ∀ {Fine Coarse Recharted Outcome}
    (observer : Glue.ObserverWithFibre Fine Coarse)
    (rechart : Coarse → Recharted)
    {consumer : Fine → Outcome} →
  INF.NonFactorabilityWitness
    (Glue.observe observer)
    consumer →
  INF.FactorsThrough
    (Glue.observe (rechartObserver observer rechart))
    consumer →
  ⊥
rechartCannotRecoverObserverFibreDistinction
    observer rechart witness =
  INF.rechartingCannotRecoverErasedPhenomenon
    rechart witness

observerFibreDistinctionSurvivesRechart :
  ∀ {Fine Coarse Recharted Outcome}
    (observer : Glue.ObserverWithFibre Fine Coarse)
    (rechart : Coarse → Recharted)
    {consumer : Fine → Outcome} →
  ObserverFibreDistinction observer consumer →
  ObserverFibreDistinction
    (rechartObserver observer rechart)
    consumer
observerFibreDistinctionSurvivesRechart
    observer rechart witness =
  observer-fibre-distinction
    (left witness)
    (right witness)
    (cong rechart (sameObservation witness))
    (consumerDistinguishes witness)

record HyperformObserverFactorisationBoundary : Set where
  constructor hyperform-observer-factorisation-boundary
  field
    everyConsumerFactorsThroughCoarseObserver : Bool
    adequacyIsConsumerIndexed : Bool
    canonicalConsumerDescentSpineReused : Bool
    fibreCollisionMayWitnessInformationLoss : Bool
    sufficientRepairMustSeparateWitnessedCollision : Bool
    postcompositionCanRecoverErasedDistinction : Bool
    richerIndependentContextMayRequireSeparateAnalysis : Bool

open HyperformObserverFactorisationBoundary public

canonicalHyperformObserverFactorisationBoundary :
  HyperformObserverFactorisationBoundary
canonicalHyperformObserverFactorisationBoundary =
  hyperform-observer-factorisation-boundary
    false true true true true false true
