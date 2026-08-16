module DASHI.Governance.EmpiricalGenealogyRound3Regression where

open import DASHI.Core.Prelude

import DASHI.Governance.EvidenceGradedGenealogyCore as Genealogy
import DASHI.Governance.EvidenceGradedGenealogyCasesExact as Cases
import DASHI.Governance.JohnPaperClaimPromotionAuditExact as Paper
import DASHI.Governance.PalantirProcurementLegibilityAdapterExact as Palantir
import DASHI.Governance.MinimalSufficientObservationGovernanceExact as Minimal
import DASHI.Governance.MultidimensionalContestabilityAccessExact as Access
import DASHI.Governance.DependentReligiousEntrapmentCandidateExact as Entrapment
import DASHI.Governance.EvolvingCapacityReligiousAutonomyExact as Capacity
import DASHI.Governance.CoercionConfinementLegalSeparationExact as Legal
import DASHI.Governance.ColonialCarceralDependencyAuthorityBridgeExact as Colonial

------------------------------------------------------------------------
-- Focused local-kernel regression root.
--
-- Suggested local command:
--   agda -i . DASHI/Governance/EmpiricalGenealogyRound3Regression.agda
------------------------------------------------------------------------

tobaccoFoodHasGradeAStrongEdge :
  Genealogy.StrongEvidenceEdge Cases.tobaccoToFoodTransfer
tobaccoFoodHasGradeAStrongEdge = Cases.tobaccoToFoodIsStrong

tobaccoClimateHasGradeBStrongEdge :
  Genealogy.StrongEvidenceEdge Cases.tobaccoToClimateHistoricalContinuity
tobaccoClimateHasGradeBStrongEdge = Cases.tobaccoToClimateIsStrong

wellnessAntiVaxAdjacencyDoesNotBecomeStrongTransfer :
  Genealogy.StrongEvidenceEdge Cases.wellnessToAntiVaxAdjacency → ⊥
wellnessAntiVaxAdjacencyDoesNotBecomeStrongTransfer =
  Cases.wellnessAdjacencyIsNotStrongHistoricalTransfer

tradwifeAltRightCandidateStillNeedsEvidence :
  Cases.CandidateConnectionPromotesToStrongGenealogy → ⊥
tradwifeAltRightCandidateStillNeedsEvidence =
  Cases.candidateConnectionDoesNotPromoteWithoutReceipt

paperFraudReceiptNotInstalled :
  Paper.JohnPaperPromotionAudit.fraudExternalLegalReceiptInstalled
    Paper.canonicalJohnPaperPromotionAudit
  ≡ false
paperFraudReceiptNotInstalled = refl

paperBatteryReceiptNotInstalled :
  Paper.JohnPaperPromotionAudit.batteryExternalLegalReceiptInstalled
    Paper.canonicalJohnPaperPromotionAudit
  ≡ false
paperBatteryReceiptNotInstalled = refl

paperModernSlaveryReceiptNotInstalled :
  Paper.JohnPaperPromotionAudit.modernSlaveryExternalLegalReceiptInstalled
    Paper.canonicalJohnPaperPromotionAudit
  ≡ false
paperModernSlaveryReceiptNotInstalled = refl

paperLegalPromotionRequiresJurisdictionReceipt :
  Paper.JohnPaperPromotionAudit.legalPromotionRequiresJurisdictionSpecificReceipt
    Paper.canonicalJohnPaperPromotionAudit
  ≡ true
paperLegalPromotionRequiresJurisdictionReceipt = refl

palantirProcurementEvidenceExists :
  Palantir.PalantirProcurementAdapterBoundary.procurementEvidenceInstalled
    Palantir.canonicalPalantirProcurementAdapterBoundary
  ≡ true
palantirProcurementEvidenceExists = refl

palantirAsymmetryStillUnconstructed :
  Palantir.PalantirProcurementAdapterBoundary.subjectInstitutionAsymmetryWitnessInstalled
    Palantir.canonicalPalantirProcurementAdapterBoundary
  ≡ false
palantirAsymmetryStillUnconstructed = refl

canonicalFutureQuotientHasMinimalityDirection :
  Minimal.MinimalObservationBoundary.canonicalFutureCodeFactorsThroughEverySectionedSafeProjection
    Minimal.canonicalMinimalObservationBoundary
  ≡ true
canonicalFutureQuotientHasMinimalityDirection = refl

scalarContestabilityBudgetCanHideBottleneck :
  Access.ResourceAccessWithin Access.bottleneckDemand Access.spreadBudget → ⊥
scalarContestabilityBudgetCanHideBottleneck =
  Access.aggregateSufficiencyDoesNotEstablishCoordinateAccess

------------------------------------------------------------------------
-- Entrapment/capacity/legal cross-pollination regressions.
------------------------------------------------------------------------

ordinaryTeachingDoesNotEqualEntrapment :
  Entrapment.DependentReligiousEntrapmentBoundary.ordinaryReligiousTeachingEqualsEntrapment
    Entrapment.canonicalDependentReligiousEntrapmentBoundary
  ≡ false
ordinaryTeachingDoesNotEqualEntrapment = refl

entrapmentMechanismsCanIncludeBelongingAndDivineSanction :
  Entrapment.DependentReligiousEntrapmentBoundary.familyBelongingPenaltyCanBeRelevantMechanism
    Entrapment.canonicalDependentReligiousEntrapmentBoundary
  ≡ true
entrapmentMechanismsCanIncludeBelongingAndDivineSanction = refl

age18IsNotReligiousConsentSwitch :
  Capacity.EvolvingCapacityReligiousAutonomyBoundary.fixedAge18ReligiousConsentSwitch
    Capacity.canonicalEvolvingCapacityReligiousAutonomyBoundary
  ≡ false
age18IsNotReligiousConsentSwitch = refl

formationBeforeEpistemicIndependenceIsRelevant :
  Capacity.EvolvingCapacityReligiousAutonomyBoundary.formationBeforeEpistemicIndependenceRelevant
    Capacity.canonicalEvolvingCapacityReligiousAutonomyBoundary
  ≡ true
formationBeforeEpistemicIndependenceIsRelevant = refl

psychologicalCoercionDoesNotEqualSlavery :
  Legal.CoercionConfinementLegalBoundary.socialEntrapmentEqualsSlavery
    Legal.canonicalCoercionConfinementLegalBoundary
  ≡ false
psychologicalCoercionDoesNotEqualSlavery = refl

servitudeStillNeedsLabourOrServicesReceipt :
  Legal.CoercionConfinementLegalBoundary.servitudeRequiresAdditionalLabourOrServicesReceipt
    Legal.canonicalCoercionConfinementLegalBoundary
  ≡ true
servitudeStillNeedsLabourOrServicesReceipt = refl

colonialCarceralComparisonDoesNotCollapseDomains :
  Colonial.ColonialCarceralDependencyBoundary.colonialSystemEqualsCarceralSystem
    Colonial.canonicalColonialCarceralDependencyBoundary
  ≡ false
colonialCarceralComparisonDoesNotCollapseDomains = refl

sharedDependencyAuthorityExitTopologyIsAvailable :
  Colonial.ColonialCarceralDependencyBoundary.dependencyAuthorityExitTopologyShared
    Colonial.canonicalColonialCarceralDependencyBoundary
  ≡ true
sharedDependencyAuthorityExitTopologyIsAvailable = refl
