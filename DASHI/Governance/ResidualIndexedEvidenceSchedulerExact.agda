module DASHI.Governance.ResidualIndexedEvidenceSchedulerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as MDL
import DASHI.Core.LiveSetParetoExperimentSchedulerExact as Live
import DASHI.Core.ExpectedFibreReductionCostExact as Reduction
import DASHI.Core.ActionabilityCostedExperimentChoiceExact as Choice
import DASHI.Governance.QuotientDefectResidualRouting as Residual

------------------------------------------------------------------------
-- RESIDUAL-INDEXED ACTIVE EVIDENCE SCHEDULER
--
-- Reuses the repo-native live-experiment carrier and hard relevance/authority
-- gates.  Governance adds residual targeting and a four-axis search chart:
-- acquisition burden, unpaid provenance, redundant coordinates, and remaining
-- consumer gap.  These are search coordinates, not truth/ethics/authority.
------------------------------------------------------------------------

record ResidualEvidenceProblem : Set₁ where
  constructor residualEvidenceProblem
  field
    liveProblem : Live.LiveExperimentProblem
    unpaidProvenance : Live.Experiment liveProblem → Nat
    redundantCoordinates : Live.Experiment liveProblem → Nat
    remainingConsumerGap : Live.Experiment liveProblem → Nat
    targetsResidual :
      Live.Experiment liveProblem → Residual.ResidualKind → Bool
    residualUnresolved : Residual.ResidualKind → Bool
    acquisitionReference : Live.Experiment liveProblem → String

open ResidualEvidenceProblem public

asResidualMDLProblem : ResidualEvidenceProblem → MDL.ConsumerMDLProblem
asResidualMDLProblem P =
  MDL.consumerMDLProblem
    (Live.Experiment (liveProblem P))
    (λ e → Reduction.authorityAdmissible
      (Live.candidate (liveProblem P) e) ≡ true)
    (λ e → Reduction.consumerRelevant
      (Live.candidate (liveProblem P) e) ≡ true)
    (λ e → Choice.cost
      (Reduction.move (Live.candidate (liveProblem P) e)))
    (λ _ _ → ⊤)
    (acquisitionReference P)
    "residual-evidence acquisition/search code"
    "consumer-relative unresolved provenance-policy residual"

data ResidualEvidenceAxis : Set where
  acquisitionBurdenAxis : ResidualEvidenceAxis
  unpaidProvenanceAxis : ResidualEvidenceAxis
  redundantCoordinateAxis : ResidualEvidenceAxis
  remainingConsumerGapAxis : ResidualEvidenceAxis

residualEvidenceCosts :
  (P : ResidualEvidenceProblem) →
  MDL.CostHyperfabric (asResidualMDLProblem P)
residualEvidenceCosts P =
  MDL.costHyperfabric ResidualEvidenceAxis score axisRef
  where
    score : ResidualEvidenceAxis → Live.Experiment (liveProblem P) → Nat
    score acquisitionBurdenAxis e =
      Choice.cost (Reduction.move (Live.candidate (liveProblem P) e))
    score unpaidProvenanceAxis e = unpaidProvenance P e
    score redundantCoordinateAxis e = redundantCoordinates P e
    score remainingConsumerGapAxis e = remainingConsumerGap P e

    axisRef : ResidualEvidenceAxis → String
    axisRef acquisitionBurdenAxis = "declared acquisition/search burden"
    axisRef unpaidProvenanceAxis = "unpaid provenance burden"
    axisRef redundantCoordinateAxis = "redundant-coordinate burden"
    axisRef remainingConsumerGapAxis = "remaining consumer gap"

record ResidualTargetWitness
    (P : ResidualEvidenceProblem)
    (e : Live.Experiment (liveProblem P)) : Set where
  constructor residualTargetWitness
  field
    residualKind : Residual.ResidualKind
    residualStillUnresolved : residualUnresolved P residualKind ≡ true
    experimentTargetsResidual : targetsResidual P e residualKind ≡ true

open ResidualTargetWitness public

record ResidualParetoChoice
    (P : ResidualEvidenceProblem)
    (selected : Live.Experiment (liveProblem P)) : Set₁ where
  constructor residualParetoChoice
  field
    pareto : MDL.ParetoAdmissible (residualEvidenceCosts P) selected
    targetsLiveResidual : ResidualTargetWitness P selected

open ResidualParetoChoice public

------------------------------------------------------------------------
-- Pareto membership retains the underlying live-set hard gates.  An experiment
-- cannot win because of low burden if it is authority-inadmissible or irrelevant
-- to the consumer.
------------------------------------------------------------------------

selectedExperimentAdmitted :
  ∀ {P selected} →
  ResidualParetoChoice P selected →
  Live.Admitted (liveProblem P) selected
selectedExperimentAdmitted choice =
  let eligible = MDL.selectedEligible (pareto choice)
  in proj₂ eligible , proj₁ eligible

selectedExperimentTargetsUnresolvedResidual :
  ∀ {P selected} →
  ResidualParetoChoice P selected →
  ResidualTargetWitness P selected
selectedExperimentTargetsUnresolvedResidual = targetsLiveResidual

record ResidualEvidenceSchedulerBoundary : Set where
  constructor residual-evidence-scheduler-boundary
  field
    authorityGatePrecedesPareto : Bool
    consumerRelevanceGatePrecedesPareto : Bool
    selectedExperimentTargetsLiveResidual : Bool
    axesAreSyntheticSearchCoordinates : Bool
    cheapestExperimentAutomaticallyWins : Bool
    maximalNominalReductionCreatesAuthority : Bool
    selectionCreatesEmpiricalObservation : Bool

canonicalResidualEvidenceSchedulerBoundary : ResidualEvidenceSchedulerBoundary
canonicalResidualEvidenceSchedulerBoundary =
  residual-evidence-scheduler-boundary
    true true true true false false false
