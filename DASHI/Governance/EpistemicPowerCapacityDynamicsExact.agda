module DASHI.Governance.EpistemicPowerCapacityDynamicsExact where

-- A finite-resource *model* of epistemic activity, not a definition of
-- psychological exhaustion or an empirical assertion about any participant.
-- This module separates workload receipts, remaining capacity, cognitive
-- fatigue, and intentional obstruction.

open import DASHI.Core.Prelude
import DASHI.Core.IntersectionalNonFactorability as Intersection
import DASHI.Governance.EpistemicPowerHistoryAndNonSubstitutionExact as History

------------------------------------------------------------------------
-- C0: Each modelled task consumes one finite resource unit.
------------------------------------------------------------------------

capacityAfter : Nat → List History.EpistemicTask → Nat
capacityAfter available [] = available
capacityAfter zero (_ ∷ tasks) = capacityAfter zero tasks
capacityAfter (suc available) (_ ∷ tasks) =
  capacityAfter available tasks

zeroCapacityAbsorbing :
  (tasks : List History.EpistemicTask) →
  capacityAfter 0 tasks ≡ 0
zeroCapacityAbsorbing [] = refl
zeroCapacityAbsorbing (_ ∷ tasks) = zeroCapacityAbsorbing tasks

emptyHistoryPreservesCapacity :
  (available : Nat) → capacityAfter available [] ≡ available
emptyHistoryPreservesCapacity available = refl

oneUnitTwoTasksDepletes :
  capacityAfter (suc zero)
    History.reopenedAndRecommunicatedHistory ≡ zero
oneUnitTwoTasksDepletes = refl

oneUnitEmptyHistoryRetains :
  capacityAfter (suc zero) History.singleAcceptedHistory ≡ suc zero
oneUnitEmptyHistoryRetains = refl

------------------------------------------------------------------------
-- C1: Equal public conclusion, unequal post-history resource state.
------------------------------------------------------------------------

remainingOneUnit : List History.EpistemicTask → Nat
remainingOneUnit = capacityAfter (suc zero)

sameFindingDifferentResourceCapacity :
  Intersection.NonFactorabilityWitness
    History.visibleDisposition remainingOneUnit
sameFindingDifferentResourceCapacity =
  Intersection.nonFactorabilityWitness
    History.singleAcceptedHistory
    History.reopenedAndRecommunicatedHistory
    refl
    (λ ())

publicRechartCannotRecoverCapacity :
  ∀ {Recharted : Set} →
  (rechart : History.PublicDisposition → Recharted) →
  Intersection.FactorsThrough
    (λ h → rechart (History.visibleDisposition h))
    remainingOneUnit → ⊥
publicRechartCannotRecoverCapacity rechart =
  Intersection.rechartingCannotRecoverErasedPhenomenon
    rechart sameFindingDifferentResourceCapacity

------------------------------------------------------------------------
-- C2: A high task load is not definitionally cognitive fatigue.
-- Two episodes may share the same trace and resource-accounting result,
-- while their independently observed fatigue status differs.
------------------------------------------------------------------------

data FatigueObservation : Set where
  fatigueNotObserved fatigueObserved : FatigueObservation

record SituatedEpisode : Set where
  constructor situated-episode
  field
    taskTrace : List History.EpistemicTask
    fatigue : FatigueObservation

open SituatedEpisode public

demandWithoutObservedFatigue : SituatedEpisode
demandWithoutObservedFatigue =
  situated-episode
    History.reopenedAndRecommunicatedHistory fatigueNotObserved

demandWithObservedFatigue : SituatedEpisode
demandWithObservedFatigue =
  situated-episode
    History.reopenedAndRecommunicatedHistory fatigueObserved

reportedTaskTrace : SituatedEpisode → List History.EpistemicTask
reportedTaskTrace = taskTrace

observedFatigue : SituatedEpisode → FatigueObservation
observedFatigue = fatigue

sameWorkloadDifferentFatigue :
  Intersection.NonFactorabilityWitness reportedTaskTrace observedFatigue
sameWorkloadDifferentFatigue =
  Intersection.nonFactorabilityWitness
    demandWithoutObservedFatigue demandWithObservedFatigue
    refl (λ ())

workloadCannotDiagnoseFatigue :
  Intersection.FactorsThrough reportedTaskTrace observedFatigue → ⊥
workloadCannotDiagnoseFatigue =
  Intersection.witnessRulesOutEveryFlatFactorisation
    sameWorkloadDifferentFatigue

------------------------------------------------------------------------
-- C3: The source-claim boundary is structural: a boolean classifier
-- based solely on task history cannot recover independent fatigue data.
------------------------------------------------------------------------

anyTaskRechartCannotDiagnoseFatigue :
  ∀ {Recharted : Set} →
  (rechart : List History.EpistemicTask → Recharted) →
  Intersection.FactorsThrough
    (λ ep → rechart (reportedTaskTrace ep))
    observedFatigue → ⊥
anyTaskRechartCannotDiagnoseFatigue rechart =
  Intersection.rechartingCannotRecoverErasedPhenomenon
    rechart sameWorkloadDifferentFatigue
