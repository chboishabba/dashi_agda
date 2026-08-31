module DASHI.Governance.DrugGovernanceHistoricalBurdenFarCrossPollinationExact where

open import DASHI.Core.Prelude

import DASHI.Core.HistoryQualifiedSelectionTopologyExact as History
import DASHI.Core.ResponsibilityBurdenNonfactorabilityExact as Responsibility
import DASHI.Planning.NonSubstitutionalReparationExact as Repair
import DASHI.Governance.IndigenousAuthorityEnvelopeExact as Indigenous
import DASHI.Governance.SocioTechnicalPowerSelectionAssayExact as Power
import DASHI.Governance.SultanaClimateColonialityResidualExact as Climate
import DASHI.Governance.DrugGovernanceHistoricalBurdenPathExact as BurdenPath
import DASHI.Governance.DrugGovernanceBurdenPathEdgeIndexedReopeningExact as Reopening

------------------------------------------------------------------------
-- FAR CROSS-POLLINATION OF HISTORICAL BURDEN FLOW
--
-- Only theorem shape crosses domains.  Climate responsibility, labour/surplus,
-- Indigenous sovereignty, reparative axes and drug-governance burden paths are
-- not identified with one another and retain their source-specific semantics.
------------------------------------------------------------------------

data AuditDomain : Set where
  drugGovernanceAudit
  climateResponsibilityAudit
  labourPowerAudit
  indigenousAuthorityAudit
  reparativeClosureAudit
  historyQualifiedAudit
  : AuditDomain

data AuditQuestion : Set where
  whoBearsBurdenQuestion
  whoBenefitsQuestion
  whoContributedQuestion
  whoControlsRulesQuestion
  whatRepairAxisRemainsQuestion
  whatHistoryPathRemainsQuestion
  whoHoldsOriginatingAuthorityQuestion
  : AuditQuestion

auditQuestion : AuditDomain → AuditQuestion
auditQuestion drugGovernanceAudit = whatHistoryPathRemainsQuestion
auditQuestion climateResponsibilityAudit = whoContributedQuestion
auditQuestion labourPowerAudit = whoBenefitsQuestion
auditQuestion indigenousAuthorityAudit = whoHoldsOriginatingAuthorityQuestion
auditQuestion reparativeClosureAudit = whatRepairAxisRemainsQuestion
auditQuestion historyQualifiedAudit = whatHistoryPathRemainsQuestion

------------------------------------------------------------------------
-- BIDI planning surface: a detected residual suggests a probe family, but the
-- audit tradition/domain does not itself prove the empirical answer.
------------------------------------------------------------------------

data ProbeFamily : Set where
  burdenDistributionProbe
  benefitRoutingProbe
  contributionProbe
  controlTopologyProbe
  repairAxisProbe
  historyPathProbe
  sovereignAuthorityProbe
  : ProbeFamily

suggestedProbe : AuditQuestion → ProbeFamily
suggestedProbe whoBearsBurdenQuestion = burdenDistributionProbe
suggestedProbe whoBenefitsQuestion = benefitRoutingProbe
suggestedProbe whoContributedQuestion = contributionProbe
suggestedProbe whoControlsRulesQuestion = controlTopologyProbe
suggestedProbe whatRepairAxisRemainsQuestion = repairAxisProbe
suggestedProbe whatHistoryPathRemainsQuestion = historyPathProbe
suggestedProbe whoHoldsOriginatingAuthorityQuestion = sovereignAuthorityProbe

------------------------------------------------------------------------
-- Canonical theorem-bearing welds.
------------------------------------------------------------------------

historyBoundary : History.HistoryQualifiedSelectionBoundary
historyBoundary = History.canonicalHistoryQualifiedSelectionBoundary

responsibilityBoundary : Responsibility.ResponsibilityBurdenBoundary
responsibilityBoundary = Responsibility.canonicalResponsibilityBurdenBoundary

repairBoundary : Repair.NonSubstitutionBoundary
repairBoundary = Repair.canonicalNonSubstitutionBoundary

indigenousBoundary : Indigenous.IndigenousAuthorityEnvelopeBoundary
indigenousBoundary = Indigenous.canonicalIndigenousAuthorityEnvelopeBoundary

powerBoundary : Power.SocioTechnicalPowerSelectionBoundary
powerBoundary = Power.canonicalSocioTechnicalPowerSelectionBoundary

climateBoundary : Climate.SultanaClimateColonialityBoundary
climateBoundary = Climate.canonicalSultanaClimateColonialityBoundary

burdenPathBoundary : BurdenPath.HistoricalBurdenPathBoundary
burdenPathBoundary = BurdenPath.canonicalHistoricalBurdenPathBoundary

reopeningBoundary : Reopening.BurdenPathEdgeIndexedReopeningBoundary
reopeningBoundary = Reopening.canonicalBurdenPathEdgeIndexedReopeningBoundary

------------------------------------------------------------------------
-- Cross-domain non-promotions.
------------------------------------------------------------------------

data SameAggregatePromotesSameBurdenDistribution : Set where

data SameServicePromotesSamePowerTopology : Set where

data CompensationPromotesAuthorityRestoration : Set where

data AttributionPromotesSovereignty : Set where

data SameEndpointPromotesSameHistory : Set where

data DrugBurdenPathPromotesClimateCausalIdentity : Set where

data ClimateResidualPromotesDrugHistoryIdentity : Set where

sameAggregateDoesNotPromoteSameBurdenDistribution :
  SameAggregatePromotesSameBurdenDistribution → ⊥
sameAggregateDoesNotPromoteSameBurdenDistribution ()

sameServiceDoesNotPromoteSamePowerTopology :
  SameServicePromotesSamePowerTopology → ⊥
sameServiceDoesNotPromoteSamePowerTopology ()

compensationDoesNotPromoteAuthorityRestoration :
  CompensationPromotesAuthorityRestoration → ⊥
compensationDoesNotPromoteAuthorityRestoration ()

attributionDoesNotPromoteSovereignty :
  AttributionPromotesSovereignty → ⊥
attributionDoesNotPromoteSovereignty ()

sameEndpointDoesNotPromoteSameHistory :
  SameEndpointPromotesSameHistory → ⊥
sameEndpointDoesNotPromoteSameHistory ()

drugBurdenPathDoesNotPromoteClimateCausalIdentity :
  DrugBurdenPathPromotesClimateCausalIdentity → ⊥
drugBurdenPathDoesNotPromoteClimateCausalIdentity ()

climateResidualDoesNotPromoteDrugHistoryIdentity :
  ClimateResidualPromotesDrugHistoryIdentity → ⊥
climateResidualDoesNotPromoteDrugHistoryIdentity ()

------------------------------------------------------------------------
-- Shared audit invariant.
------------------------------------------------------------------------

record HistoricalBurdenFarCrossPollinationBoundary : Set where
  constructor historicalBurdenFarCrossPollinationBoundary
  field
    aggregateOutcomeDeterminesDistribution : Bool
    aggregateOutcomeDeterminesDistributionIsFalse :
      aggregateOutcomeDeterminesDistribution ≡ false
    presentEndpointDeterminesOrderedHistory : Bool
    presentEndpointDeterminesOrderedHistoryIsFalse :
      presentEndpointDeterminesOrderedHistory ≡ false
    materialCompensationSubstitutesForAuthorityRepair : Bool
    materialCompensationSubstitutesForAuthorityRepairIsFalse :
      materialCompensationSubstitutesForAuthorityRepair ≡ false
    provenanceOrAttributionTransfersSovereignty : Bool
    provenanceOrAttributionTransfersSovereigntyIsFalse :
      provenanceOrAttributionTransfersSovereignty ≡ false
    sameFunctionalSurfaceDeterminesPowerTopology : Bool
    sameFunctionalSurfaceDeterminesPowerTopologyIsFalse :
      sameFunctionalSurfaceDeterminesPowerTopology ≡ false
    auditQuestionAutomaticallyProvesEmpiricalAnswer : Bool
    auditQuestionAutomaticallyProvesEmpiricalAnswerIsFalse :
      auditQuestionAutomaticallyProvesEmpiricalAnswer ≡ false
    crossDomainProofShapeMeansDomainIdentity : Bool
    crossDomainProofShapeMeansDomainIdentityIsFalse :
      crossDomainProofShapeMeansDomainIdentity ≡ false

canonicalHistoricalBurdenFarCrossPollinationBoundary :
  HistoricalBurdenFarCrossPollinationBoundary
canonicalHistoricalBurdenFarCrossPollinationBoundary =
  historicalBurdenFarCrossPollinationBoundary
    false refl false refl false refl false refl false refl false refl false refl
