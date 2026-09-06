module DASHI.Core.CapabilityFragilityConfoundersBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- CAPABILITY FRAGILITY CONFOUNDERS, BIDI
--
-- A capability can appear concentrated or fragile for mundane organisational,
-- contractual, physical-custody or documentation reasons.  These are competing
-- explanations to test before promoting targeting or event-causation claims.
------------------------------------------------------------------------

data FragilityAxis : Set where
  organisationalReorganisation
  mergerOrAcquisition
  fundingOrProcurementChange
  contractOrIPTransition
  accessControlChange
  physicalArtifactCustody
  dataRepositoryCustody
  codificationQuality
  teamRedundancy
  externalLabourReplaceability
  supplierDependency
  facilityDependency
  scheduledRetirementOrDeparture
  ordinaryProjectSuccession
  safetyOrFailureInvestigation
  : FragilityAxis

data AxisState : Set where
  sourceBacked
  partial
  notLocated
  knownAbsent
  : AxisState

record FragilityReceipt : Set where
  constructor fragility-receipt
  field
    caseReference : String
    axis : FragilityAxis
    state : AxisState
    sourceReference : String
    boundedReading : String

open FragilityReceipt public

data FragilityReverseTarget : Set where
  acquireOrgChartBeforeAfter
  acquireMergerIntegrationRecord
  acquireFundingTimeline
  acquireContractOrIPAssignment
  acquireAccessAuditOrTransfer
  acquireHardwareCustodyRecord
  acquireRepositoryOwnership
  acquireSOPNotebookCodeCoverage
  acquireBackupRoleMatrix
  acquireRecruitmentOrReplacementEvidence
  acquireSupplierOrFacilityDependency
  acquireScheduledTransitionRecord
  acquireSafetyIncidentRecord
  : FragilityReverseTarget

record FragilityBoundary : Set where
  constructor fragility-boundary
  field
    reorganisationImpliesCapabilityLoss : Bool
    reorganisationImpliesCapabilityLossIsFalse : reorganisationImpliesCapabilityLoss ≡ false
    acquisitionImpliesTargeting : Bool
    acquisitionImpliesTargetingIsFalse : acquisitionImpliesTargeting ≡ false
    poorCodificationImpliesUniqueHolder : Bool
    poorCodificationImpliesUniqueHolderIsFalse : poorCodificationImpliesUniqueHolder ≡ false
    distributedTeamImpliesNoCriticalDependency : Bool
    distributedTeamImpliesNoCriticalDependencyIsFalse : distributedTeamImpliesNoCriticalDependency ≡ false
    mundaneTransitionMustBeTestedBeforeTargetingPromotion : Bool
    mundaneTransitionMustBeTestedBeforeTargetingPromotionIsTrue : mundaneTransitionMustBeTestedBeforeTargetingPromotion ≡ true

canonicalFragilityBoundary : FragilityBoundary
canonicalFragilityBoundary = fragility-boundary false refl false refl false refl false refl true refl
