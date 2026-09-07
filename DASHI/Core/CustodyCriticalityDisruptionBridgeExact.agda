module DASHI.Core.CustodyCriticalityDisruptionBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ApplicationCapabilityCustodyBidiExact as C
import DASHI.Core.EventTimeOperationalPossessionEvidenceExact as E
import DASHI.Core.CriticalKnowledgeConcentrationBidiExact as K
import DASHI.Core.CounterfactualDisruptionImpactExact as I
import DASHI.Core.TechnicalExternalisationDepthBidiExact as X

------------------------------------------------------------------------
-- CUSTODY -> CRITICALITY -> COUNTERFACTUAL IMPACT BRIDGE
--
-- Reconciles the newer custody/event-time refinements with the older
-- critical-knowledge, externalisation-depth and matched-departure owners.
-- The new coordinates refine evidence for existing criticality/impact axes;
-- they do not constitute a parallel theory of critical capability.
------------------------------------------------------------------------

data BridgeStage : Set where
  custodyEvidence : BridgeStage
  eventTimePossession : BridgeStage
  criticalityAssessment : BridgeStage
  counterfactualImpact : BridgeStage
  matchedDepartureComparison : BridgeStage


record CustodyCriticalityBridgeReceipt : Set where
  constructor custody-criticality-bridge-receipt
  field
    subject : String
    capability : String
    custodyCoordinate : C.CustodyCoordinate
    criticalityAxis : K.CriticalityAxis
    sourceReference : String
    boundedReading : String

open CustodyCriticalityBridgeReceipt public

record EventTimeImpactBridgeReceipt : Set where
  constructor event-time-impact-bridge-receipt
  field
    subject : String
    capability : String
    eventTimeEvidence : E.ContinuityEvidenceKind
    impactAxis : I.ImpactAxis
    sourceReference : String
    boundedReading : String

open EventTimeImpactBridgeReceipt public

------------------------------------------------------------------------
-- Conservative coordinate routing.
------------------------------------------------------------------------

custodyToCriticality : C.CustodyCoordinate -> K.CriticalityAxis
custodyToCriticality C.physicalApparatus = K.replacementDifficulty
custodyToCriticality C.rawData = K.nonPublicness
custodyToCriticality C.reducedData = K.nonPublicness
custodyToCriticality C.sourceRepository = K.replacementDifficulty
custodyToCriticality C.calibrationArchive = K.replacementDifficulty
custodyToCriticality C.configurationArchive = K.replacementDifficulty
custodyToCriticality C.qualificationArchive = K.integrationBreadth
custodyToCriticality C.failureHistory = K.replacementDifficulty
custodyToCriticality C.notebooks = K.replacementDifficulty
custodyToCriticality C.intellectualProperty = K.nonPublicness
custodyToCriticality C.accessCredential = K.nonPublicness
custodyToCriticality C.facilityAccess = K.integrationBreadth
custodyToCriticality C.supplierRelationship = K.integrationBreadth

eventTimeToImpact : E.ContinuityEvidenceKind -> I.ImpactAxis
eventTimeToImpact E.historicalRole = I.noMeasuredImpact
eventTimeToImpact E.memorialRoleSummary = I.noMeasuredImpact
eventTimeToImpact E.publicationAffiliation = I.noMeasuredImpact
eventTimeToImpact E.currentEmploymentOrAppointment = I.programmeReorganisation
eventTimeToImpact E.activeProjectRoster = I.knowledgeTransferGap
eventTimeToImpact E.facilityOrRepositoryAccess = I.replacementLatency
eventTimeToImpact E.calibrationOrConfigurationCustody = I.uniqueQualificationLoss
eventTimeToImpact E.sameCarrierOperationalUse = I.technicalPerformanceLoss

------------------------------------------------------------------------
-- Existing externalisation owner remains the public-side control.
------------------------------------------------------------------------

record ExternalisationCriticalityBridge
    (profile : X.TechnicalExternalisationProfile) : Set where
  constructor externalisation-criticality-bridge
  field
    publicDepthReference : String
    residualCriticalityStillRequiresReceipts : Bool
    residualCriticalityStillRequiresReceiptsIsTrue :
      residualCriticalityStillRequiresReceipts ≡ true

open ExternalisationCriticalityBridge public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

record CustodyCriticalityDisruptionBoundary : Set where
  constructor custody-criticality-disruption-boundary
  field
    custodyImpliesUniqueness : Bool
    custodyImpliesUniquenessIsFalse : custodyImpliesUniqueness ≡ false
    eventTimeRoleImpliesReplacementDifficulty : Bool
    eventTimeRoleImpliesReplacementDifficultyIsFalse : eventTimeRoleImpliesReplacementDifficulty ≡ false
    replacementDifficultyImpliesDisproportionateDisruption : Bool
    replacementDifficultyImpliesDisproportionateDisruptionIsFalse :
      replacementDifficultyImpliesDisproportionateDisruption ≡ false
    disproportionateDisruptionImpliesTargeting : Bool
    disproportionateDisruptionImpliesTargetingIsFalse :
      disproportionateDisruptionImpliesTargeting ≡ false
    deepExternalisationImpliesNoResidualCriticalKnowledge : Bool
    deepExternalisationImpliesNoResidualCriticalKnowledgeIsFalse :
      deepExternalisationImpliesNoResidualCriticalKnowledge ≡ false
    matchedDepartureControlRequiredForStrongImpactPromotion : Bool
    matchedDepartureControlRequiredForStrongImpactPromotionIsTrue :
      matchedDepartureControlRequiredForStrongImpactPromotion ≡ true

canonicalCustodyCriticalityDisruptionBoundary : CustodyCriticalityDisruptionBoundary
canonicalCustodyCriticalityDisruptionBoundary = custody-criticality-disruption-boundary
  false refl
  false refl
  false refl
  false refl
  false refl
  true refl

data ReconciledReverseTarget : Set where
  acquireSameCarrierCustody : ReconciledReverseTarget
  acquireEventTimeOperationalUse : ReconciledReverseTarget
  acquireUniquenessReceipt : ReconciledReverseTarget
  acquireNonPublicnessReceipt : ReconciledReverseTarget
  acquireIntegrationBreadthReceipt : ReconciledReverseTarget
  acquireReplacementDifficultyReceipt : ReconciledReverseTarget
  acquireMeasuredDepartureImpact : ReconciledReverseTarget
  acquireMatchedOrdinaryDepartureControl : ReconciledReverseTarget
