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
  organisationalReorganisation : FragilityAxis
  mergerOrAcquisition : FragilityAxis
  fundingOrProcurementChange : FragilityAxis
  contractOrIPTransition : FragilityAxis
  accessControlChange : FragilityAxis
  physicalArtifactCustody : FragilityAxis
  dataRepositoryCustody : FragilityAxis
  codificationQuality : FragilityAxis
  teamRedundancy : FragilityAxis
  externalLabourReplaceability : FragilityAxis
  supplierDependency : FragilityAxis
  facilityDependency : FragilityAxis
  scheduledRetirementOrDeparture : FragilityAxis
  ordinaryProjectSuccession : FragilityAxis
  safetyOrFailureInvestigation : FragilityAxis


data AxisState : Set where
  sourceBacked : AxisState
  partial : AxisState
  notLocated : AxisState
  knownAbsent : AxisState


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
  acquireOrgChartBeforeAfter : FragilityReverseTarget
  acquireMergerIntegrationRecord : FragilityReverseTarget
  acquireFundingTimeline : FragilityReverseTarget
  acquireContractOrIPAssignment : FragilityReverseTarget
  acquireAccessAuditOrTransfer : FragilityReverseTarget
  acquireHardwareCustodyRecord : FragilityReverseTarget
  acquireRepositoryOwnership : FragilityReverseTarget
  acquireSOPNotebookCodeCoverage : FragilityReverseTarget
  acquireBackupRoleMatrix : FragilityReverseTarget
  acquireRecruitmentOrReplacementEvidence : FragilityReverseTarget
  acquireSupplierOrFacilityDependency : FragilityReverseTarget
  acquireScheduledTransitionRecord : FragilityReverseTarget
  acquireSafetyIncidentRecord : FragilityReverseTarget


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
