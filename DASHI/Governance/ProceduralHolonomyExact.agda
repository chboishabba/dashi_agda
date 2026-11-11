module DASHI.Governance.ProceduralHolonomyExact where

-- Original DASHI finite procedural-loop / situated-workload weld.
-- Draws on the existing epistemic-task owner and relational descent
-- cycle-residual analogues. No claim of connection curvature, topological
-- non-flatness, biological harm, malicious controller or legal liability.
--
-- A CLOSED loop in formal status is compatible with a NONZERO accumulated
-- workload fibre. This does not make the individual steps unlawful.
-- Here admissibility is a SYNTHETIC policy, not original case evidence.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Governance.EpistemicPowerHistoryAndNonSubstitutionExact as Work

data ProceduralStanding : Set where
  cleared reviewOpen : ProceduralStanding

data Request : Set where
  openReview closeReview : Request

-- The local admissibility predicate here is wholly synthetic and must not
-- be mistaken for a jurisdictional or procedural authorization.
data LocalPermission : ProceduralStanding → Request → Set where
  permitOpening : LocalPermission cleared openReview
  permitClosure : LocalPermission reviewOpen closeReview

nextStanding : (before : ProceduralStanding) →
  (request : Request) → LocalPermission before request →
  ProceduralStanding
nextStanding cleared openReview permitOpening = reviewOpen
nextStanding reviewOpen closeReview permitClosure = cleared

-- Each locally allowed action can incur *positive* epistemic work.
-- The work ledger remains separate from the public standing projection.
taskFor : Request → Work.EpistemicTask
taskFor openReview = Work.retainBelief
taskFor closeReview = Work.communicateBelief

record SituatedState : Set where
  constructor situated-state
  field
    publicStanding : ProceduralStanding
    taskLog : List Work.EpistemicTask

open SituatedState public

applyPermitted :
  (state : SituatedState) →
  (request : Request) →
  LocalPermission (publicStanding state) request →
  SituatedState
applyPermitted (situated-state standing tasks) request permission =
  situated-state
    (nextStanding standing request permission)
    (taskFor request ∷ tasks)

initial : SituatedState
initial = situated-state cleared []

afterOpening : SituatedState
afterOpening = applyPermitted initial openReview permitOpening

afterClosure : SituatedState
afterClosure = applyPermitted afterOpening closeReview permitClosure

closedBaseLoop :
  publicStanding afterClosure ≡ publicStanding initial
closedBaseLoop = refl

locallyPermittedOpening :
  LocalPermission (publicStanding initial) openReview
locallyPermittedOpening = permitOpening

locallyPermittedClosure :
  LocalPermission (publicStanding afterOpening) closeReview
locallyPermittedClosure = permitClosure

-- This is a finite *ledger* residual. It is not a clinical allostatic
-- measurement and does not assign any joule, cortisol or damage unit.
workload : SituatedState → Work.TaskBurden
workload state = Work.foldTaskHistory (taskLog state)

finalRetentionOne :
  Work.retaining (workload afterClosure) ≡ 1
finalRetentionOne = refl

finalCommunicationOne :
  Work.communicating (workload afterClosure) ≡ 1
finalCommunicationOne = refl

initialRetentionZero :
  Work.retaining (workload initial) ≡ 0
initialRetentionZero = refl

sameStandingNonzeroWorkload :
  Work.retaining (workload initial) ≡
  Work.retaining (workload afterClosure) → ⊥
sameStandingNonzeroWorkload ()

-- Different histories can be indistinguishable to a status-only observer.
data ProcedureHistory : Set where
  noReview completedReview : ProcedureHistory

finalState : ProcedureHistory → SituatedState
finalState noReview = initial
finalState completedReview = afterClosure

standingObserver : ProcedureHistory → ProceduralStanding
standingObserver history = publicStanding (finalState history)

retentionConsumer : ProcedureHistory → Nat
retentionConsumer history =
  Work.retaining (workload (finalState history))

samePublicStanding :
  standingObserver noReview ≡ standingObserver completedReview
samePublicStanding = refl

differentRetention :
  retentionConsumer noReview ≡ retentionConsumer completedReview → ⊥
differentRetention ()

closedStandingDoesNotDetermineAccumulatedWork :
  NF.NonFactorabilityWitness standingObserver retentionConsumer
closedStandingDoesNotDetermineAccumulatedWork =
  NF.nonFactorabilityWitness
    noReview completedReview
    samePublicStanding differentRetention

noStandingOnlyWorkloadDecoder :
  NF.FactorsThrough standingObserver retentionConsumer → ⊥
noStandingOnlyWorkloadDecoder =
  NF.witnessRulesOutEveryFlatFactorisation
    closedStandingDoesNotDetermineAccumulatedWork

anyStandingOnlyRechartStillLosesWork :
  ∀ {Chart : Set}
  (chart : ProceduralStanding → Chart) →
  NF.FactorsThrough
    (λ history → chart (standingObserver history))
    retentionConsumer → ⊥
anyStandingOnlyRechartStillLosesWork chart =
  NF.rechartingCannotRecoverErasedPhenomenon
    chart closedStandingDoesNotDetermineAccumulatedWork

-- Distinct independent external evidence gates. Their types are not
-- instantiated here, and no claim of person-specific harm or wrongdoing
-- follows from the numerical synthetic task history.
record ProceduralEvidenceGates (Case : Set) : Set₁ where
  field
    authenticatedOriginalCase : Case → Set
    independentlyValidLocalPermissions : Case → Set
    authenticatedChronology : Case → Set
    verifiedSubjectWorkload : Case → Set
    counterfactualBurdenComparison : Case → Set
    sourceSpecificBiologicalAssessment : Case → Set
    independentControllerProvenance : Case → Set
    applicableLegalAuthority : Case → Set

-- A fibre displacement on a closed base path only proves path-dependent
-- state, NOT the topological non-flatness of a connection. A true holonomy
-- theorem needs an invertible parallel transport on the SAME fibre,
-- a specified base loop and compositional laws. Work accumulation here
-- is generally non-invertible, so it is not Wilson-loop holonomy.
