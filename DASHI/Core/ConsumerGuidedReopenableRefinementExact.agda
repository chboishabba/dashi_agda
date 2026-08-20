module DASHI.Core.ConsumerGuidedReopenableRefinementExact where

------------------------------------------------------------------------
-- PURPOSE
--
-- Project-neutral counterexample-guided refinement kernel extracted from the
-- convergent Animalexic / SeaMeInIt / LES architecture.
--
-- Literature vocabulary:
--   Edmund M. Clarke, Orna Grumberg, Somesh Jha, Yuan Lu, Helmut Veith,
--   "Counterexample-Guided Abstraction Refinement", CAV 2000,
--   DOI 10.1007/10722167_15.
--   Edmund M. Clarke et al.,
--   "Counterexample-guided abstraction refinement for symbolic model checking",
--   JACM 50(5), 2003, DOI 10.1145/876638.876643.
--
-- These citations motivate the abstraction/refinement vocabulary only.  The
-- exact types and proofs below are DASHI constructions and do not import proof
-- authority from those papers.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.List.Base using (length)

import DASHI.Core.ReopenableConsumerInterventionKernelExact as Base
import DASHI.Core.GenericFuturePartitionRefinementExact as Future

------------------------------------------------------------------------
-- 1. A refinement factors the old projection through the new one.  Strictness
--    is witnessed constructively by one old fibre that the new projection
--    separates.
------------------------------------------------------------------------

record StrictProjectionRefinement
    {Fine Old New : Set}
    (oldProject : Fine → Old)
    (newProject : Fine → New) : Set₁ where
  constructor strictProjectionRefinement
  field
    forget : New → Old
    oldFactorsThroughNew :
      ∀ fine → oldProject fine ≡ forget (newProject fine)

    splitLeft splitRight : Fine
    sameOldFibre : oldProject splitLeft ≡ oldProject splitRight
    separatedByNew :
      newProject splitLeft ≡ newProject splitRight → ⊥

open StrictProjectionRefinement public

record ConsumerGuidedRefinement
    {Fine Old New Output : Set}
    (oldProject : Fine → Old)
    (newProject : Fine → New)
    (consume : Fine → Output) : Set₁ where
  constructor consumerGuidedRefinement
  field
    projectionRefinement :
      StrictProjectionRefinement oldProject newProject
    consumerSeparatesWitness :
      consume (splitLeft projectionRefinement)
      ≡ consume (splitRight projectionRefinement) → ⊥

open ConsumerGuidedRefinement public

consumerGuidedOldDescentDefect :
  ∀ {Fine Old New Output}
    {oldProject : Fine → Old}
    {newProject : Fine → New}
    {consume : Fine → Output} →
  ConsumerGuidedRefinement oldProject newProject consume →
  Base.ConsumerDescentDefect oldProject consume
consumerGuidedOldDescentDefect refinement =
  Base.consumerDescentDefect
    (splitLeft (projectionRefinement refinement))
    (splitRight (projectionRefinement refinement))
    (sameOldFibre (projectionRefinement refinement))
    (consumerSeparatesWitness refinement)

consumerGuidedRefinementRefutesOldDescent :
  ∀ {Fine Old New Output}
    {oldProject : Fine → Old}
    {newProject : Fine → New}
    {consume : Fine → Output} →
  ConsumerGuidedRefinement oldProject newProject consume →
  Base.ConsumerDescent oldProject consume →
  ⊥
consumerGuidedRefinementRefutesOldDescent refinement descent =
  Base.consumerDescentDefectContradictsDescent
    descent
    (consumerGuidedOldDescentDefect refinement)

------------------------------------------------------------------------
-- 2. Local refinement can promise that unaffected old fibres remain intact.
--    This is stronger than merely saying the new code contains more bits.
------------------------------------------------------------------------

record LocalProjectionRefinement
    {Fine Old New : Set}
    (oldProject : Fine → Old)
    (newProject : Fine → New)
    (Affected : Fine → Set) : Set₁ where
  constructor localProjectionRefinement
  field
    strict :
      StrictProjectionRefinement oldProject newProject
    unaffectedFibresPreserved :
      ∀ left right →
      ¬ Affected left →
      ¬ Affected right →
      oldProject left ≡ oldProject right →
      newProject left ≡ newProject right

open LocalProjectionRefinement public

------------------------------------------------------------------------
-- 3. A finite action trace is an experiment.  If it separates two states at
--    the final observation, the corresponding bounded behavioural equivalence
--    is impossible at that trace length.
------------------------------------------------------------------------

record TraceSeparatingWitness
    {State Action Observation : Set}
    (observe : State → Observation)
    (step : Action → State → State)
    (left right : State) : Set₁ where
  constructor traceSeparatingWitness
  field
    actions : List Action
    finalObservationSeparates :
      observe (Future.run step actions left)
      ≡ observe (Future.run step actions right) → ⊥

open TraceSeparatingWitness public

traceSeparationRefutesDepth :
  ∀ {State Action Observation}
    {observe : State → Observation}
    {step : Action → State → State}
    {left right : State} →
  (witness : TraceSeparatingWitness observe step left right) →
  Future.RefinesToDepth
    (length (actions witness)) observe step left right →
  ⊥
traceSeparationRefutesDepth witness related =
  finalObservationSeparates witness
    (Future.traceObservationFromDepth (actions witness) related)

record OneStepSeparatingWitness
    {State Action Observation : Set}
    (observe : State → Observation)
    (step : Action → State → State)
    (left right : State) : Set₁ where
  constructor oneStepSeparatingWitness
  field
    sameObservationNow : observe left ≡ observe right
    separatingAction : Action
    separatesAfterAction :
      observe (step separatingAction left)
      ≡ observe (step separatingAction right) → ⊥

open OneStepSeparatingWitness public

oneStepWitnessGivesDepthZero :
  ∀ {State Action Observation}
    {observe : State → Observation}
    {step : Action → State → State}
    {left right : State} →
  OneStepSeparatingWitness observe step left right →
  Future.RefinesToDepth zero observe step left right
oneStepWitnessGivesDepthZero witness = sameObservationNow witness

oneStepWitnessRefutesDepthOne :
  ∀ {State Action Observation}
    {observe : State → Observation}
    {step : Action → State → State}
    {left right : State} →
  OneStepSeparatingWitness observe step left right →
  Future.RefinesToDepth (suc zero) observe step left right →
  ⊥
oneStepWitnessRefutesDepthOne witness related =
  separatesAfterAction witness
    (proj₂ related (separatingAction witness))

------------------------------------------------------------------------
-- 4. Robust bounded equivalence quantifies the same behavioural relation over
--    a declared context/scenario family.  It is intentionally not a
--    probability distribution over contexts.
------------------------------------------------------------------------

RobustEquivalentToDepth :
  ∀ {Context State Action Observation : Set} →
  Nat →
  (Context → State → Observation) →
  (Context → Action → State → State) →
  State → State → Set
RobustEquivalentToDepth depth observe step left right =
  ∀ context →
  Future.RefinesToDepth depth
    (observe context) (step context) left right

robustEquivalentAtContext :
  ∀ {Context State Action Observation depth}
    {observe : Context → State → Observation}
    {step : Context → Action → State → State}
    {left right : State} →
  RobustEquivalentToDepth depth observe step left right →
  (context : Context) →
  Future.RefinesToDepth depth
    (observe context) (step context) left right
robustEquivalentAtContext robust context = robust context

------------------------------------------------------------------------
-- 5. Approximate descent is consumer-safe only relative to a declared decision
--    margin/stability relation.  The core does not invent a metric.
------------------------------------------------------------------------

record ApproximateConsumerDescent
    {Fine Coarse Output : Set}
    (project : Fine → Coarse)
    (consume : Fine → Output)
    (Within : Output → Output → Set) : Set₁ where
  constructor approximateConsumerDescent
  field
    quotientConsumer : Coarse → Output
    approximationBound :
      ∀ fine →
      Within (consume fine) (quotientConsumer (project fine))

open ApproximateConsumerDescent public

record ConsumerDecisionMargin
    {Output Decision : Set}
    (Within : Output → Output → Set)
    (decide : Output → Decision) : Set₁ where
  constructor consumerDecisionMargin
  field
    stableInsideMargin :
      ∀ actual approximate →
      Within actual approximate →
      decide actual ≡ decide approximate

open ConsumerDecisionMargin public

approximateDescentPreservesDecision :
  ∀ {Fine Coarse Output Decision}
    {project : Fine → Coarse}
    {consume : Fine → Output}
    {Within : Output → Output → Set}
    {decide : Output → Decision} →
  (descent : ApproximateConsumerDescent project consume Within) →
  ConsumerDecisionMargin Within decide →
  ∀ fine →
  decide (consume fine)
  ≡ decide (quotientConsumer descent (project fine))
approximateDescentPreservesDecision descent margin fine =
  stableInsideMargin margin
    (consume fine)
    (quotientConsumer descent (project fine))
    (approximationBound descent fine)

------------------------------------------------------------------------
-- 6. Low-margin / large-defect regions can be declared as the only places in
--    which refinement is allowed to split an old fibre.
------------------------------------------------------------------------

record ConsumerGuidedRefinementRegion
    {Fine Old New : Set}
    (oldProject : Fine → Old)
    (newProject : Fine → New) : Set₁ where
  constructor consumerGuidedRefinementRegion
  field
    NeedsRefinement : Fine → Set
    localRefinement :
      LocalProjectionRefinement oldProject newProject NeedsRefinement

open ConsumerGuidedRefinementRegion public

------------------------------------------------------------------------
-- Shared boundary.
------------------------------------------------------------------------

record ConsumerGuidedRefinementBoundary : Set where
  constructor consumerGuidedRefinementBoundary
  field
    defectIsASeparatingWitnessNotMerelyAScore : Bool
    refinementMustFactorOldProjection : Bool
    unaffectedFibresNeedNotBeRecomputed : Bool
    finiteTraceSeparationRefutesBoundedEquivalence : Bool
    robustnessIsRelativeToDeclaredContexts : Bool
    approximateDescentNeedsConsumerMargin : Bool
    localRefinementMayFollowDecisionInstability : Bool
    refinementDoesNotCreateDomainTruth : Bool

open ConsumerGuidedRefinementBoundary public

canonicalConsumerGuidedRefinementBoundary :
  ConsumerGuidedRefinementBoundary
canonicalConsumerGuidedRefinementBoundary =
  consumerGuidedRefinementBoundary
    true true true true true true true true
