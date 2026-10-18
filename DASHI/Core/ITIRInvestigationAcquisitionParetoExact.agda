module DASHI.Core.ITIRInvestigationAcquisitionParetoExact where

-- Generic ITIR-INV-1 acquisition loop.
-- Canonical dominance now matches the Rust runtime directly:
--   information/dependency/coverage/novelty maximise; lawful cost minimises.
-- No bounded `1000 ∸ gain` embedding remains in the authority path.

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.EvidenceAcquisitionSelectiveReopeningExact as Acquisition

data InvestigationPriorityAxis : Set where
  informationGainAxis : InvestigationPriorityAxis
  dependencyClosureAxis : InvestigationPriorityAxis
  residualCoverageAxis : InvestigationPriorityAxis
  provenanceNoveltyAxis : InvestigationPriorityAxis
  acquisitionCostAxis : InvestigationPriorityAxis

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

-- Direct runtime-equivalent mixed orientation:
-- left weakly dominates right iff it is >= on every benefit axis and <= on cost.
record MixedWeaklyDominates
    (left right : InvestigationCandidate) : Set where
  constructor mixed-weakly-dominates
  field
    informationNoWorse : informationGain right ≤ informationGain left
    dependencyNoWorse : dependencyClosureImpact right ≤ dependencyClosureImpact left
    coverageNoWorse : residualCoverage right ≤ residualCoverage left
    noveltyNoWorse : provenanceNovelty right ≤ provenanceNovelty left
    costNoWorse : lawfulResourceCost left ≤ lawfulResourceCost right

open MixedWeaklyDominates public

data StrictImprovement
    (left right : InvestigationCandidate) : Set where
  informationStrict : informationGain right < informationGain left → StrictImprovement left right
  dependencyStrict : dependencyClosureImpact right < dependencyClosureImpact left → StrictImprovement left right
  coverageStrict : residualCoverage right < residualCoverage left → StrictImprovement left right
  noveltyStrict : provenanceNovelty right < provenanceNovelty left → StrictImprovement left right
  costStrict : lawfulResourceCost left < lawfulResourceCost right → StrictImprovement left right

record MixedStrictlyDominates
    (left right : InvestigationCandidate) : Set where
  constructor mixed-strictly-dominates
  field
    weak : MixedWeaklyDominates left right
    strictSomewhere : StrictImprovement left right

open MixedStrictlyDominates public

MixedParetoAdmissible : InvestigationCandidate → Set₁
MixedParetoAdmissible selected =
  (candidate : InvestigationCandidate) →
  MixedWeaklyDominates candidate selected →
  MixedWeaklyDominates selected candidate

-- Compatibility name: callers asking for the canonical INV Pareto notion now
-- receive the direct mixed-orientation relation, not a transformed loss space.
InvestigationParetoAdmissible : InvestigationCandidate → Set₁
InvestigationParetoAdmissible = MixedParetoAdmissible

axisReference : InvestigationPriorityAxis → String
axisReference informationGainAxis = "expected discrimination / information gain (maximise)"
axisReference dependencyClosureAxis = "dependency-closure impact (maximise)"
axisReference residualCoverageAxis = "unpaid residual coverage (maximise)"
axisReference provenanceNoveltyAxis = "provenance novelty / independence gain (maximise)"
axisReference acquisitionCostAxis = "lawful acquisition / reviewer / resource cost (minimise)"

record DirectMixedParetoView : Set where
  constructor direct-mixed-pareto-view
  field
    declaredDimension : Nat
    dimensionReceiptReference : String
    axisSemanticReference : InvestigationPriorityAxis → String
    scalarScoreUsed : Bool
    scalarScoreUsedIsFalse : scalarScoreUsed ≡ false
    visualisationReference : String

investigationParetoView : DirectMixedParetoView
investigationParetoView =
  direct-mixed-pareto-view
    5
    "ITIR-INV-1 five direct mixed-orientation acquisition axes"
    axisReference
    false refl
    "Dioxus/wgpu may visualise the frontier but does not rank it"

-- Regression specimen above the old hidden 1000 ceiling. Under the former
-- truncating subtraction both information values collapsed to zero loss.
aboveBoundBetter : InvestigationCandidate
aboveBoundBetter = investigation-candidate
  "candidate:1201" "obligation:1" "route:1201" "access:public"
  "genealogy:1" "axis:reviewed"
  1001 7 5 3 2
  true refl false refl false refl

aboveBoundWorse : InvestigationCandidate
aboveBoundWorse = investigation-candidate
  "candidate:1000" "obligation:1" "route:1000" "access:public"
  "genealogy:2" "axis:reviewed"
  1000 7 5 3 2
  true refl false refl false refl

above1000DominancePreserved : MixedStrictlyDominates aboveBoundBetter aboveBoundWorse
above1000DominancePreserved =
  mixed-strictly-dominates
    (mixed-weakly-dominates
      (≤-step ≤-refl)
      ≤-refl
      ≤-refl
      ≤-refl
      ≤-refl)
    (informationStrict ≤-refl)

record InvestigationAcquisitionBoundary : Set where
  constructor investigation-acquisition-boundary
  field
    residualMayGenerateTargetedObligation : Bool
    residualMayGenerateTargetedObligationIsTrue : residualMayGenerateTargetedObligation ≡ true
    scalarScoreRequired : Bool
    scalarScoreRequiredIsFalse : scalarScoreRequired ≡ false
    priorityCreatesSourceTruth : Bool
    priorityCreatesSourceTruthIsFalse : priorityCreatesSourceTruth ≡ false
    priorityCreatesAccessAuthority : Bool
    priorityCreatesAccessAuthorityIsFalse : priorityCreatesAccessAuthority ≡ false
    notLocatedMeansKnownAbsent : Bool
    notLocatedMeansKnownAbsentIsFalse : notLocatedMeansKnownAbsent ≡ false
    sourceSimilarityCreatesIndependence : Bool
    sourceSimilarityCreatesIndependenceIsFalse : sourceSimilarityCreatesIndependence ≡ false
    acquiredEvidenceReopensUnrelatedConsumers : Bool
    acquiredEvidenceReopensUnrelatedConsumersIsFalse : acquiredEvidenceReopensUnrelatedConsumers ≡ false
    formalRuntimeFrontierUsesSameAxisOrientation : Bool
    formalRuntimeFrontierUsesSameAxisOrientationIsTrue : formalRuntimeFrontierUsesSameAxisOrientation ≡ true

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
    true refl

-- Existing generic selective-reopening theorem remains the dependency owner.
genericAcquisitionReopening :
  ∀ {Artifact}
    {graph : Acquisition.AcquisitionDependencyGraph Artifact}
    {changed target : Artifact} →
  Acquisition.Depends graph changed target →
  Acquisition.SelectiveAcquisitionReopening graph changed target
genericAcquisitionReopening = Acquisition.oneEdgeAcquisitionReopening
