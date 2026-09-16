module DASHI.Culture.CohnInstitutionalLeastCoordinateRepairExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as MDL
import DASHI.Core.ConsumerSafeRefinementPromotionExact as Promotion
import DASHI.Core.AffectedDependencyClosureExact as Dependency
import DASHI.Culture.CohnInstitutionalComposedConsumerAdequacyExact as Composed

------------------------------------------------------------------------
-- LEAST-COORDINATE INSTITUTIONAL REPAIR
--
-- Thin application of the repository's existing local-repair / minimum-
-- eligible / Pareto machinery.  The finite candidate family and synthetic
-- costs are DASHI synthesis.  They are not empirical institutional costs,
-- source credibility scores, legal authority, or historical claims.
--
-- Starting point:
--   evidence x authority is sufficient for the decision query but fails the
--   downstream intervention-audit query because consequence varies inside a
--   decision fibre.
--
-- Repair discipline:
--   retain exactly the missing consequence coordinate first; do not retain an
--   unrelated coordinate merely because it is available.
------------------------------------------------------------------------

data InstitutionalRepairCandidate : Set where
  decisionOnlyCandidate : InstitutionalRepairCandidate
  consequenceQualifiedCandidate : InstitutionalRepairCandidate
  overRetainedCandidate : InstitutionalRepairCandidate

candidateReference : InstitutionalRepairCandidate → String
candidateReference decisionOnlyCandidate =
  "decision observer retaining evidence and authority only"
candidateReference consequenceQualifiedCandidate =
  "decision observer plus the consequence coordinate required by the intervention-audit consumer"
candidateReference overRetainedCandidate =
  "consequence-qualified observer plus an additional unrelated institutional-normality coordinate"

candidateDescriptionLength : InstitutionalRepairCandidate → Nat
candidateDescriptionLength decisionOnlyCandidate = 2
candidateDescriptionLength consequenceQualifiedCandidate = 3
candidateDescriptionLength overRetainedCandidate = 4

RepairAdmissible : InstitutionalRepairCandidate → Set
RepairAdmissible decisionOnlyCandidate = ⊤
RepairAdmissible consequenceQualifiedCandidate = ⊤
RepairAdmissible overRetainedCandidate = ⊤

InterventionAuditAdequate : InstitutionalRepairCandidate → Set
InterventionAuditAdequate decisionOnlyCandidate = ⊥
InterventionAuditAdequate consequenceQualifiedCandidate = ⊤
InterventionAuditAdequate overRetainedCandidate = ⊤

data InstitutionalRepairRefines :
  InstitutionalRepairCandidate → InstitutionalRepairCandidate → Set where
  addConsequenceCoordinate :
    InstitutionalRepairRefines decisionOnlyCandidate consequenceQualifiedCandidate
  addUnrelatedNormalityCoordinate :
    InstitutionalRepairRefines consequenceQualifiedCandidate overRetainedCandidate

interventionRepairProblem : MDL.ConsumerMDLProblem
interventionRepairProblem = MDL.consumerMDLProblem
  InstitutionalRepairCandidate
  RepairAdmissible
  InterventionAuditAdequate
  candidateDescriptionLength
  InstitutionalRepairRefines
  candidateReference
  "repository-local retained-coordinate count; not money, labour, latency, empirical effort, truth probability, or institutional value"
  "intervention-audit consumer requiring decision disposition plus consequence profile"

------------------------------------------------------------------------
-- The existing composed-consumer collision is the reason the coarse candidate
-- is excluded.  We retain it as the application witness/reference, but the
-- generic repair theorem remains repository-local DASHI structure.
------------------------------------------------------------------------

decisionOnlyCounterexample :
  MDL.ConsumerCounterexample interventionRepairProblem decisionOnlyCandidate
decisionOnlyCounterexample = MDL.consumerCounterexample
  ⊤
  tt
  (λ adequate → adequate)
  "evidence x authority preserves the decision disposition but erases the consequence distinction required by interventionAuditQuery"
  "CohnInstitutionalComposedConsumerAdequacyExact.decisionInterventionDefect"

decisionToConsequenceRepair :
  MDL.LocalRefinementRepair
    interventionRepairProblem
    decisionOnlyCandidate
    consequenceQualifiedCandidate
decisionToConsequenceRepair = MDL.localRefinementRepair
  decisionOnlyCounterexample
  addConsequenceCoordinate
  tt
  tt
  "retain the consequence profile that separates the intervention-audit collision; do not reopen unrelated coordinates merely to make the observer richer"

------------------------------------------------------------------------
-- Minimum eligible repair.
------------------------------------------------------------------------

consequenceNoLongerThanAnyEligible :
  (candidate : InstitutionalRepairCandidate) →
  RepairAdmissible candidate →
  InterventionAuditAdequate candidate →
  candidateDescriptionLength consequenceQualifiedCandidate ≤
  candidateDescriptionLength candidate
consequenceNoLongerThanAnyEligible decisionOnlyCandidate admissible ()
consequenceNoLongerThanAnyEligible consequenceQualifiedCandidate admissible adequate = ≤-refl
consequenceNoLongerThanAnyEligible overRetainedCandidate admissible adequate =
  s≤s (s≤s (s≤s z≤n))

consequenceMinimalEligible :
  MDL.MinimalEligibleDescription
    interventionRepairProblem
    consequenceQualifiedCandidate
consequenceMinimalEligible = MDL.minimalEligibleDescription
  tt
  tt
  consequenceNoLongerThanAnyEligible
  "consequenceQualifiedCandidate is the least retained-coordinate repair in this declared finite candidate family"

------------------------------------------------------------------------
-- Pareto layer.  Lower is better on each repository-local synthetic axis.
------------------------------------------------------------------------

data RepairCostAxis : Set where
  retainedCoordinateBurden : RepairCostAxis
  redundantCoordinateBurden : RepairCostAxis
  remainingConsumerGap : RepairCostAxis

repairCost : RepairCostAxis → InstitutionalRepairCandidate → Nat
repairCost retainedCoordinateBurden decisionOnlyCandidate = 2
repairCost retainedCoordinateBurden consequenceQualifiedCandidate = 3
repairCost retainedCoordinateBurden overRetainedCandidate = 4
repairCost redundantCoordinateBurden decisionOnlyCandidate = 0
repairCost redundantCoordinateBurden consequenceQualifiedCandidate = 0
repairCost redundantCoordinateBurden overRetainedCandidate = 1
repairCost remainingConsumerGap decisionOnlyCandidate = 1
repairCost remainingConsumerGap consequenceQualifiedCandidate = 0
repairCost remainingConsumerGap overRetainedCandidate = 0

repairAxisReference : RepairCostAxis → String
repairAxisReference retainedCoordinateBurden =
  "synthetic count-like retained-coordinate burden; not measured institutional effort"
repairAxisReference redundantCoordinateBurden =
  "synthetic burden for coordinates unnecessary to the declared consumer"
repairAxisReference remainingConsumerGap =
  "synthetic remaining query-adequacy gap; not truth, importance, legal merit, or expected utility"

interventionRepairCosts : MDL.CostHyperfabric interventionRepairProblem
interventionRepairCosts =
  MDL.costHyperfabric RepairCostAxis repairCost repairAxisReference

consequenceWeaklyDominatesAnyEligible :
  (candidate : InstitutionalRepairCandidate) →
  RepairAdmissible candidate →
  InterventionAuditAdequate candidate →
  MDL.WeaklyDominates
    interventionRepairCosts
    consequenceQualifiedCandidate
    candidate
consequenceWeaklyDominatesAnyEligible decisionOnlyCandidate admissible ()
consequenceWeaklyDominatesAnyEligible consequenceQualifiedCandidate admissible adequate axis = ≤-refl
consequenceWeaklyDominatesAnyEligible overRetainedCandidate admissible adequate retainedCoordinateBurden =
  s≤s (s≤s (s≤s z≤n))
consequenceWeaklyDominatesAnyEligible overRetainedCandidate admissible adequate redundantCoordinateBurden =
  z≤n
consequenceWeaklyDominatesAnyEligible overRetainedCandidate admissible adequate remainingConsumerGap =
  z≤n

consequenceParetoAdmissible :
  MDL.ParetoAdmissible
    interventionRepairCosts
    consequenceQualifiedCandidate
consequenceParetoAdmissible = MDL.paretoAdmissible
  (tt , tt)
  (λ candidate eligible candidateDominates →
    consequenceWeaklyDominatesAnyEligible
      candidate
      (proj₁ eligible)
      (proj₂ eligible))
  "after hard consumer adequacy, consequenceQualifiedCandidate is Pareto-admissible against the over-retained alternative"

canonicalLeastCoordinatePromotion :
  Promotion.ConsumerSafeRefinementPromotion
    interventionRepairCosts
    decisionOnlyCandidate
    consequenceQualifiedCandidate
canonicalLeastCoordinatePromotion =
  Promotion.consumerSafeRefinementPromotion
    decisionToConsequenceRepair
    consequenceMinimalEligible
    consequenceParetoAdmissible

------------------------------------------------------------------------
-- Dependency-derived reopening scope.
--
-- This is an application relation only.  It reuses the canonical proof-bearing
-- reopening calculus and does not introduce a second revision semantics.
------------------------------------------------------------------------

data RepairScopeArtifact : Set where
  consequenceCoordinateArtifact : RepairScopeArtifact
  interventionAuditArtifact : RepairScopeArtifact
  institutionalNormalityCoordinateArtifact : RepairScopeArtifact


data RepairScopeDepends : RepairScopeArtifact → RepairScopeArtifact → Set where
  consequenceFeedsInterventionAudit :
    RepairScopeDepends consequenceCoordinateArtifact interventionAuditArtifact

consequenceRepairReopensInterventionAudit :
  Dependency.ReopeningObligation
    RepairScopeDepends
    consequenceCoordinateArtifact
    interventionAuditArtifact
consequenceRepairReopensInterventionAudit =
  Dependency.oneEdgeCreatesReopeningObligation consequenceFeedsInterventionAudit

------------------------------------------------------------------------
-- Direct parent receipt: the repair coordinate really is the coordinate that
-- the previous finite collision proved was missing.
------------------------------------------------------------------------

parentDecisionObserverStillFailsAudit :
  Composed.decisionAdequacyImpliesInterventionAuditAdequacy
    Composed.canonicalInstitutionalComposedConsumerAdequacyBoundary ≡ false
parentDecisionObserverStillFailsAudit = refl

parentJoinedConsequenceRepairsAudit :
  Composed.joinedObserverMayRepairDeclaredConsumer
    Composed.canonicalInstitutionalComposedConsumerAdequacyBoundary ≡ true
parentJoinedConsequenceRepairsAudit = refl

------------------------------------------------------------------------
-- Boundary / attribution firewall.
------------------------------------------------------------------------

record LeastCoordinateRepairBoundary : Set where
  constructor leastCoordinateRepairBoundary
  field
    failedConsumerMayDriveLocalRepair : Bool
    failedConsumerMayDriveLocalRepairIsTrue :
      failedConsumerMayDriveLocalRepair ≡ true

    leastEligibleRepairMayBeSelected : Bool
    leastEligibleRepairMayBeSelectedIsTrue :
      leastEligibleRepairMayBeSelected ≡ true

    richerObserverAutomaticallyPreferred : Bool
    richerObserverAutomaticallyPreferredIsFalse :
      richerObserverAutomaticallyPreferred ≡ false

    repairReopensDeclaredDependentAudit : Bool
    repairReopensDeclaredDependentAuditIsTrue :
      repairReopensDeclaredDependentAudit ≡ true

    leastRepairAutomaticallyReopensUnrelatedNormality : Bool
    leastRepairAutomaticallyReopensUnrelatedNormalityIsFalse :
      leastRepairAutomaticallyReopensUnrelatedNormality ≡ false

    leastRepairCreatesUniversalFutureAdequacy : Bool
    leastRepairCreatesUniversalFutureAdequacyIsFalse :
      leastRepairCreatesUniversalFutureAdequacy ≡ false

    leastRepairCreatesAuthority : Bool
    leastRepairCreatesAuthorityIsFalse :
      leastRepairCreatesAuthority ≡ false

    syntheticCostIsMeasuredInstitutionalBurden : Bool
    syntheticCostIsMeasuredInstitutionalBurdenIsFalse :
      syntheticCostIsMeasuredInstitutionalBurden ≡ false

    externalDecisionTheoryOwnsDASHIRepairTheorem : Bool
    externalDecisionTheoryOwnsDASHIRepairTheoremIsFalse :
      externalDecisionTheoryOwnsDASHIRepairTheorem ≡ false

open LeastCoordinateRepairBoundary public

canonicalLeastCoordinateRepairBoundary : LeastCoordinateRepairBoundary
canonicalLeastCoordinateRepairBoundary =
  leastCoordinateRepairBoundary
    true refl
    true refl
    false refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
