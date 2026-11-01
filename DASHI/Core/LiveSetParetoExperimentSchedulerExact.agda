module DASHI.Core.LiveSetParetoExperimentSchedulerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.ExpectedFibreReductionCostExact as Reduction
import DASHI.Core.ActionabilityCostedExperimentChoiceExact as Choice
import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as Pareto

------------------------------------------------------------------------
-- LIVE-SET PARETO EXPERIMENT SCHEDULER
--
-- Hard gates first: consumer relevance and authority admissibility.
-- Within the admitted stratum, experiments are compared on declared axes.
-- Here the two canonical axes are residual-survival penalty and resource cost.
------------------------------------------------------------------------

record LiveExperimentProblem : Set₁ where
  constructor liveExperimentProblem
  field
    Experiment : Set
    candidate : Experiment → Reduction.FibreReductionCostCandidate
    residualSurvivalPenalty : Experiment → Nat
    experimentReference : Experiment → String

open LiveExperimentProblem public

Admitted : (P : LiveExperimentProblem) → Experiment P → Set
Admitted P e =
  Reduction.consumerRelevant (candidate P e) ≡ true
  × Reduction.authorityAdmissible (candidate P e) ≡ true

asMDLProblem : LiveExperimentProblem → Pareto.ConsumerMDLProblem
asMDLProblem P =
  Pareto.consumerMDLProblem
    (Experiment P)
    (λ e → Reduction.authorityAdmissible (candidate P e) ≡ true)
    (λ e → Reduction.consumerRelevant (candidate P e) ≡ true)
    (λ e → Choice.cost (Reduction.move (candidate P e)))
    (λ _ _ → ⊤)
    (experimentReference P)
    "live experiment resource-cost code"
    "declared residual/consumer context"

data LiveExperimentAxis : Set where
  residualSurvivalAxis : LiveExperimentAxis
  resourceCostAxis : LiveExperimentAxis

liveCosts :
  (P : LiveExperimentProblem) →
  Pareto.CostHyperfabric (asMDLProblem P)
liveCosts P =
  Pareto.costHyperfabric LiveExperimentAxis score axisRef
  where
    score : LiveExperimentAxis → Experiment P → Nat
    score residualSurvivalAxis e = residualSurvivalPenalty P e
    score resourceCostAxis e = Choice.cost (Reduction.move (candidate P e))

    axisRef : LiveExperimentAxis → String
    axisRef residualSurvivalAxis = "remaining live-fibre penalty"
    axisRef resourceCostAxis = "declared experiment/search resource cost"

ParetoLiveExperiment :
  (P : LiveExperimentProblem) → Experiment P → Set₁
ParetoLiveExperiment P e = Pareto.ParetoAdmissible (liveCosts P) e

------------------------------------------------------------------------
-- Exact fixture: two admitted experiments are Pareto-incomparable.
-- Cheap/weak wins cost; costly/strong wins residual elimination.
------------------------------------------------------------------------

data ToyExperiment : Set where cheapExperiment strongExperiment : ToyExperiment

toyCandidate : ToyExperiment → Reduction.FibreReductionCostCandidate
toyCandidate cheapExperiment = Reduction.cheapWeak
toyCandidate strongExperiment = Reduction.costlyStrong

toySurvivalPenalty : ToyExperiment → Nat
toySurvivalPenalty cheapExperiment = 2
toySurvivalPenalty strongExperiment = 0

toyReference : ToyExperiment → String
toyReference cheapExperiment = "cheap weak live-set discriminator"
toyReference strongExperiment = "costly strong live-set discriminator"

toyProblem : LiveExperimentProblem
toyProblem = liveExperimentProblem ToyExperiment toyCandidate toySurvivalPenalty toyReference

cheapAdmitted : Admitted toyProblem cheapExperiment
cheapAdmitted = refl , refl

strongAdmitted : Admitted toyProblem strongExperiment
strongAdmitted = refl , refl

cheapDoesNotWeaklyDominateStrong :
  Pareto.WeaklyDominates (liveCosts toyProblem) cheapExperiment strongExperiment → ⊥
cheapDoesNotWeaklyDominateStrong dominates =
  twoNotLeZero (dominates residualSurvivalAxis)
  where
    twoNotLeZero : 2 ≤ 0 → ⊥
    twoNotLeZero ()

strongDoesNotWeaklyDominateCheap :
  Pareto.WeaklyDominates (liveCosts toyProblem) strongExperiment cheapExperiment → ⊥
strongDoesNotWeaklyDominateCheap dominates =
  fourNotLeOne (dominates resourceCostAxis)
  where
    fourNotLeOne : 4 ≤ 1 → ⊥
    fourNotLeOne ()

record LiveSetParetoSchedulerBoundary : Set where
  constructor liveSetParetoSchedulerBoundary
  field
    cheapestAdmittedExperimentAlwaysParetoDominates : Bool
    cheapestAdmittedExperimentAlwaysParetoDominatesIsFalse :
      cheapestAdmittedExperimentAlwaysParetoDominates ≡ false
    strongestReductionAlwaysParetoDominates : Bool
    strongestReductionAlwaysParetoDominatesIsFalse :
      strongestReductionAlwaysParetoDominates ≡ false
    authorityIsHardGateBeforeParetoComparison : Bool
    authorityIsHardGateBeforeParetoComparisonIsTrue :
      authorityIsHardGateBeforeParetoComparison ≡ true
    consumerRelevanceIsHardGateBeforeParetoComparison : Bool
    consumerRelevanceIsHardGateBeforeParetoComparisonIsTrue :
      consumerRelevanceIsHardGateBeforeParetoComparison ≡ true
    paretoChoiceCreatesUniqueScientificTruth : Bool
    paretoChoiceCreatesUniqueScientificTruthIsFalse :
      paretoChoiceCreatesUniqueScientificTruth ≡ false

canonicalLiveSetParetoSchedulerBoundary : LiveSetParetoSchedulerBoundary
canonicalLiveSetParetoSchedulerBoundary =
  liveSetParetoSchedulerBoundary false refl false refl true refl true refl false refl
