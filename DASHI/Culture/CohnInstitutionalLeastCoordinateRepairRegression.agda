module DASHI.Culture.CohnInstitutionalLeastCoordinateRepairRegression where

open import DASHI.Core.Prelude

import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as MDL
import DASHI.Core.ConsumerSafeRefinementPromotionExact as Promotion
import DASHI.Core.AffectedDependencyClosureExact as Dependency
import DASHI.Culture.CohnInstitutionalLeastCoordinateRepairExact as Repair

leastRepairIsConsumerSafePromotion :
  Promotion.ConsumerSafeRefinementPromotion
    Repair.interventionRepairCosts
    Repair.decisionOnlyCandidate
    Repair.consequenceQualifiedCandidate
leastRepairIsConsumerSafePromotion = Repair.canonicalLeastCoordinatePromotion

leastRepairIsMinimalEligible :
  MDL.MinimalEligibleDescription
    Repair.interventionRepairProblem
    Repair.consequenceQualifiedCandidate
leastRepairIsMinimalEligible = Repair.consequenceMinimalEligible

leastRepairIsParetoAdmissible :
  MDL.ParetoAdmissible
    Repair.interventionRepairCosts
    Repair.consequenceQualifiedCandidate
leastRepairIsParetoAdmissible = Repair.consequenceParetoAdmissible

consequenceRepairReopensAudit :
  Dependency.ReopeningObligation
    Repair.RepairScopeDepends
    Repair.consequenceCoordinateArtifact
    Repair.interventionAuditArtifact
consequenceRepairReopensAudit = Repair.consequenceRepairReopensInterventionAudit

leastRepairDoesNotMeanUniversalAdequacy :
  Repair.leastRepairCreatesUniversalFutureAdequacy
    Repair.canonicalLeastCoordinateRepairBoundary ≡ false
leastRepairDoesNotMeanUniversalAdequacy = refl

leastRepairDoesNotCreateAuthority :
  Repair.leastRepairCreatesAuthority
    Repair.canonicalLeastCoordinateRepairBoundary ≡ false
leastRepairDoesNotCreateAuthority = refl

syntheticCostDoesNotBecomeEmpiricalBurden :
  Repair.syntheticCostIsMeasuredInstitutionalBurden
    Repair.canonicalLeastCoordinateRepairBoundary ≡ false
syntheticCostDoesNotBecomeEmpiricalBurden = refl
