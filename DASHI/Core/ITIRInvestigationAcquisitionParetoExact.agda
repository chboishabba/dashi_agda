module DASHI.Core.ITIRInvestigationAcquisitionParetoExact where

-- Generic ITIR-INV-1 acquisition loop.
-- Generalises the already-existing ESD/Eskridge pattern without importing
-- their domain assumptions:
--
--   residual -> targeted acquisition obligation -> non-scalar Pareto frontier
--            -> lawful acquisition -> source receipt -> selective reopening
--
-- Priority never creates truth, admission or access authority.

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.EvidenceAcquisitionSelectiveReopeningExact as Acquisition
import DASHI.Core.AffectedDependencyClosureExact as Dependency
import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as Pareto
import DASHI.Core.NDimParetoHyperfabricExact as NDim

data InvestigationPriorityAxis : Set where
  informationLoss : InvestigationPriorityAxis
  dependencyClosureLoss : InvestigationPriorityAxis
  residualCoverageLoss : InvestigationPriorityAxis
  provenanceNoveltyLoss : InvestigationPriorityAxis
  acquisitionCost : InvestigationPriorityAxis

record InvestigationCandidate : Set where
  constructor investigation-candidate
  field
    candidateRef : String
    obligationRef : String
    routeRef : String
    accessConstraintRef : String
    genealogyRef : String
    axisReceiptRef : String

    informationGain : Nat
    dependencyClosureImpact : Nat
    residualCoverage : Nat
    provenanceNovelty : Nat
    lawfulResourceCost : Nat

    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    createsSourceTruth : Bool
    createsSourceTruthIsFalse : createsSourceTruth ≡ false
    createsAccessAuthority : Bool
    createsAccessAuthorityIsFalse : createsAccessAuthority ≡ false

open InvestigationCandidate public

investigationProblem : Pareto.ConsumerMDLProblem
investigationProblem =
  Pareto.consumerMDLProblem InvestigationCandidate
    (λ x → candidateRef x)

investigationCosts : Pareto.CostHyperfabric investigationProblem
investigationCosts =
  Pareto.costHyperfabric InvestigationPriorityAxis cost
  where
  -- First four are maximisation objectives encoded as loss against a
  -- common declared ceiling.  The concrete runtime is responsible for
  -- preserving the declared axis semantics and must not scalarise them.
  cost : InvestigationPriorityAxis → InvestigationCandidate → Nat
  cost informationLoss x = 1000 ∸ informationGain x
  cost dependencyClosureLoss x = 1000 ∸ dependencyClosureImpact x
  cost residualCoverageLoss x = 1000 ∸ residualCoverage x
  cost provenanceNoveltyLoss x = 1000 ∸ provenanceNovelty x
  cost acquisitionCost x = lawfulResourceCost x

InvestigationParetoAdmissible : InvestigationCandidate → Set₁
InvestigationParetoAdmissible =
  Pareto.ParetoAdmissible investigationCosts

investigationParetoView : NDim.NDimParetoView investigationCosts
investigationParetoView =
  NDim.ndimParetoView
    5
    "ITIR-INV-1 five declared acquisition axes"
    axisRef
    true
    "Dioxus/wgpu may visualise the frontier but does not rank it"
  where
  axisRef : InvestigationPriorityAxis → String
  axisRef informationLoss = "expected discrimination/information gain"
  axisRef dependencyClosureLoss = "dependency-closure impact"
  axisRef residualCoverageLoss = "unpaid residual coverage"
  axisRef provenanceNoveltyLoss = "provenance novelty / independence gain"
  axisRef acquisitionCost = "lawful acquisition/reviewer/resource cost"

record InvestigationAcquisitionBoundary : Set where
  constructor investigation-acquisition-boundary
  field
    residualMayGenerateTargetedObligation : Bool
    residualMayGenerateTargetedObligationIsTrue :
      residualMayGenerateTargetedObligation ≡ true

    scalarScoreRequired : Bool
    scalarScoreRequiredIsFalse : scalarScoreRequired ≡ false

    priorityCreatesSourceTruth : Bool
    priorityCreatesSourceTruthIsFalse : priorityCreatesSourceTruth ≡ false

    priorityCreatesAccessAuthority : Bool
    priorityCreatesAccessAuthorityIsFalse :
      priorityCreatesAccessAuthority ≡ false

    notLocatedMeansKnownAbsent : Bool
    notLocatedMeansKnownAbsentIsFalse :
      notLocatedMeansKnownAbsent ≡ false

    sourceSimilarityCreatesIndependence : Bool
    sourceSimilarityCreatesIndependenceIsFalse :
      sourceSimilarityCreatesIndependence ≡ false

    acquiredEvidenceReopensUnrelatedConsumers : Bool
    acquiredEvidenceReopensUnrelatedConsumersIsFalse :
      acquiredEvidenceReopensUnrelatedConsumers ≡ false

canonicalInvestigationAcquisitionBoundary : InvestigationAcquisitionBoundary
canonicalInvestigationAcquisitionBoundary =
  investigation-acquisition-boundary
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl

-- Existing generic selective-reopening theorem is the actual dependency owner.
genericAcquisitionReopening :
  ∀ {Artifact}
    {graph : Acquisition.AcquisitionDependencyGraph Artifact}
    {changed target : Artifact} →
  Acquisition.Depends graph changed target →
  Acquisition.SelectiveAcquisitionReopening graph changed target
genericAcquisitionReopening =
  Acquisition.oneEdgeAcquisitionReopening

-- Full Pareto dominance always implies dominance in a consumer-selected axis
-- projection, but not conversely.
projectedInvestigationDominance :
  (projection : NDim.AxisProjection investigationCosts) →
  ∀ {left right} →
  Pareto.WeaklyDominates investigationCosts left right →
  NDim.ProjectedWeaklyDominates projection left right
projectedInvestigationDominance =
  NDim.fullDominanceImpliesProjected
