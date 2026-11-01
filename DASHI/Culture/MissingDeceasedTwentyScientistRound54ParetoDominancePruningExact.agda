module DASHI.Culture.MissingDeceasedTwentyScientistRound54ParetoDominancePruningExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Nat using (_≤_; z≤n; s≤s)

import DASHI.Culture.MissingDeceasedTwentyScientistRound53ParetoAcquisitionSchedulerExact as R53
import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as Pareto

------------------------------------------------------------------------
-- ROUND 54: ELIGIBLE-BUT-DOMINATED ACQUISITION PRUNING
--
-- Round 53 hard-gated irrelevant broad biography gathering and exposed several
-- Pareto-incomparable live tasks.  This owner pays the additional scheduler
-- obligation requested by the programme: show that an acquisition can be
-- admissible, consumer-relevant and residual-attacking, yet still be kept off
-- the CURRENT critical path because another admitted acquisition dominates it
-- on every declared axis.
------------------------------------------------------------------------

data PruningTask : Set where
  chavezExactCrossing : PruningTask
  lowYieldExactObjectSnowball : PruningTask

record PruningTaskMetadata : Set where
  constructor pruning-task-metadata
  field
    taskReference : String
    residualReference : String
    acquisitionReference : String
    deferNotDeleteReference : String

open PruningTaskMetadata public

metadata : PruningTask → PruningTaskMetadata
metadata chavezExactCrossing = pruning-task-metadata
  "Anthony Chavez Scorpius/DARHT exact engineering crossing"
  "R52/R53 retained-person same-object Scorpius/DARHT residual"
  "search task/drawing/review/work-package carriers with named personnel"
  "if later paid or blocked, rerun scheduler and reopen sibling tasks as required"
metadata lowYieldExactObjectSnowball = pruning-task-metadata
  "generic lower-yield exact-object snowball"
  "a real retained-person exact-object residual outside the current highest-alpha leaves"
  "search broad project/grant outputs that may eventually expose a retained crossing"
  "still required in portfolio; merely deferred while dominated on the current live state"

------------------------------------------------------------------------
-- Both tasks pass the hard gates.
------------------------------------------------------------------------

pruningProblem : Pareto.ConsumerMDLProblem
pruningProblem = Pareto.consumerMDLProblem
  PruningTask
  (λ _ → ⊤)
  (λ _ → ⊤)
  declaredBurden
  (λ _ _ → ⊤)
  (λ t → taskReference (metadata t))
  "fixture-local ordinal burden used only after admission"
  "current exact-object acquisition scheduler"
  where
    declaredBurden : PruningTask → Nat
    declaredBurden chavezExactCrossing = 2
    declaredBurden lowYieldExactObjectSnowball = 4

chavezEligible : Pareto.Eligible pruningProblem chavezExactCrossing
chavezEligible = tt , tt

lowYieldSnowballEligible : Pareto.Eligible pruningProblem lowYieldExactObjectSnowball
lowYieldSnowballEligible = tt , tt

------------------------------------------------------------------------
-- Same four semantics as Round 53; lower penalty is better.
------------------------------------------------------------------------

data PruningAxis : Set where
  promotionResidualAxis : PruningAxis
  sourceOriginClosureAxis : PruningAxis
  professionalGateClosureAxis : PruningAxis
  acquisitionBurdenAxis : PruningAxis

pruningScore : PruningAxis → PruningTask → Nat
pruningScore promotionResidualAxis chavezExactCrossing = 1
pruningScore promotionResidualAxis lowYieldExactObjectSnowball = 3
pruningScore sourceOriginClosureAxis chavezExactCrossing = 1
pruningScore sourceOriginClosureAxis lowYieldExactObjectSnowball = 2
pruningScore professionalGateClosureAxis chavezExactCrossing = 2
pruningScore professionalGateClosureAxis lowYieldExactObjectSnowball = 3
pruningScore acquisitionBurdenAxis chavezExactCrossing = 2
pruningScore acquisitionBurdenAxis lowYieldExactObjectSnowball = 4

pruningAxisReference : PruningAxis → String
pruningAxisReference promotionResidualAxis = "remaining promotion residual"
pruningAxisReference sourceOriginClosureAxis = "remaining source-origin uncertainty"
pruningAxisReference professionalGateClosureAxis = "remaining professional-consumer gate debt"
pruningAxisReference acquisitionBurdenAxis = "declared acquisition burden"

pruningCosts : Pareto.CostHyperfabric pruningProblem
pruningCosts = Pareto.costHyperfabric PruningAxis pruningScore pruningAxisReference

------------------------------------------------------------------------
-- Chavez weakly dominates the lower-yield task on every declared axis.
------------------------------------------------------------------------

oneLeThree : 1 ≤ 3
oneLeThree = s≤s z≤n

oneLeTwo : 1 ≤ 2
oneLeTwo = s≤s z≤n

twoLeThree : 2 ≤ 3
twoLeThree = s≤s (s≤s z≤n)

twoLeFour : 2 ≤ 4
twoLeFour = s≤s (s≤s z≤n)

chavezDominatesLowYield :
  Pareto.WeaklyDominates pruningCosts chavezExactCrossing lowYieldExactObjectSnowball
chavezDominatesLowYield promotionResidualAxis = oneLeThree
chavezDominatesLowYield sourceOriginClosureAxis = oneLeTwo
chavezDominatesLowYield professionalGateClosureAxis = twoLeThree
chavezDominatesLowYield acquisitionBurdenAxis = twoLeFour

lowYieldCannotDominateChavez :
  Pareto.WeaklyDominates pruningCosts lowYieldExactObjectSnowball chavezExactCrossing → ⊥
lowYieldCannotDominateChavez dominates = threeNotLeOne (dominates promotionResidualAxis)
  where
    threeNotLeOne : 3 ≤ 1 → ⊥
    threeNotLeOne ()

lowYieldNotParetoAdmissible :
  Pareto.ParetoAdmissible pruningCosts lowYieldExactObjectSnowball → ⊥
lowYieldNotParetoAdmissible receipt =
  lowYieldCannotDominateChavez
    (Pareto.noStrictlyCheaperEligibleWitness receipt
      chavezExactCrossing
      chavezEligible
      chavezDominatesLowYield)

eligibleButDominatedStaysOffCurrentParetoFrontier : Bool
eligibleButDominatedStaysOffCurrentParetoFrontier = true

------------------------------------------------------------------------
-- Firewalls and rerun semantics.
------------------------------------------------------------------------

dominatedDoesNotMeanDeleted : Bool
dominatedDoesNotMeanDeleted = true

schedulerRerunsAfterResidualChange : Bool
schedulerRerunsAfterResidualChange = true

offFrontierTaskMayReturnAfterEvidenceUpdate : Bool
offFrontierTaskMayReturnAfterEvidenceUpdate = true

paretoPruningIsStateRelative : Bool
paretoPruningIsStateRelative = true

paretoPruningDoesNotCreateHistoricalIrrelevance : Bool
paretoPruningDoesNotCreateHistoricalIrrelevance = true

paretoPruningDoesNotCreateSourceAuthority : Bool
paretoPruningDoesNotCreateSourceAuthority = true

paretoPruningDoesNotPayRequirement : Bool
paretoPruningDoesNotPayRequirement = true

round54H2PaidCount : Nat
round54H2PaidCount = 0

round54H3PaidCount : Nat
round54H3PaidCount = 0

round54Reading : String
round54Reading = "Pareto now performs actual critical-path pruning in addition to hard-gate filtering. The lower-yield exact-object snowball is itself admissible, relevant and residual-attacking, but Chavez's exact Scorpius/DARHT crossing task weakly dominates it on promotion-residual, source-origin, professional-gate and acquisition-burden axes. The dominated task is deferred, not deleted: any paid, blocked or reopened residual changes the live state and triggers a fresh Pareto run."
