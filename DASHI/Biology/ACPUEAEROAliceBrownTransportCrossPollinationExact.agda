module DASHI.Biology.ACPUEAEROAliceBrownTransportCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Biology.ACPUEAEROTransportUniversalAuditExact as Universal
import DASHI.Biology.AliceBrownEducationAuditAdmissibilityCrossPollinationExact as BrownAudit
import DASHI.Biology.StudentVoiceEpistemicAgencyBridge as Voice
import DASHI.Biology.StudentIdentifiedSupportStrategiesBridge as Strategies
import DASHI.Biology.ParentAllyshipMultiObserverBridge as Multi
import DASHI.Biology.HumourOnlineEngagementFramework as Humour

------------------------------------------------------------------------
-- AERO UNIVERSAL-TRANSPORT <-> ALICE BROWN CORPUS WELD
--
-- This module does NOT use the Brown corpus as evidence against AERO's specific
-- empirical proposition.  It uses the source-bound Brown fibres as positive
-- regression cases showing why universal educational transport must preserve
-- observer, choice, context and conditional-practice coordinates.
------------------------------------------------------------------------

record UniversalTransportResidual : Set where
  constructor universalTransportResidual
  field
    universalAudit : Universal.UniversalTransportBoundary
    participantRoleUnresolved : Bool
    observerPluralityUnresolved : Bool
    localChoiceUnresolved : Bool
    conditionalContextUnresolved : Bool
    participantContestabilityUnresolved : Bool
    residualReading : String

open UniversalTransportResidual public

canonicalUniversalTransportResidual : UniversalTransportResidual
canonicalUniversalTransportResidual =
  universalTransportResidual
    Universal.canonicalUniversalTransportBoundary
    true
    true
    true
    true
    true
    "The AERO all-learners/all-classrooms assertion has a transport residual whenever the evidence chain does not separately establish whose perspectives were represented, which observer fibres were included, whether implementation depends on local learner choice, which contextual conditions are constitutive, and whether situated interpretations are contestable. Brown-derived examples demonstrate these are real education-research coordinates; they are not treated as counterevidence to AERO by themselves."

------------------------------------------------------------------------
-- Brown corpus regressions against silent universalisation.
------------------------------------------------------------------------

studentVoiceRegression : Bool
studentVoiceRegression =
  Voice.noAutomaticEpistemicAuthority
    Voice.canonicalStudentVoiceEpistemicAgencyBridge

supportChoiceRegression : Bool
supportChoiceRegression =
  Strategies.studentChoiceRequired
    Strategies.canonicalStudentIdentifiedSupportStrategiesBridge

supportNonUniversalRegression : Bool
supportNonUniversalRegression =
  Strategies.noUniversalPrescription
    Strategies.canonicalStudentIdentifiedSupportStrategiesBridge

multiObserverRegression : Bool
multiObserverRegression =
  Multi.noObserverProjectionEqualsWhole
    Multi.canonicalParentAllyshipMultiObserverBridge

humourContextRegression : Bool
humourContextRegression =
  Humour.futureWorkSeeksStudentPerspectives
    Humour.canonicalHumourFrameworkSourceSurface

------------------------------------------------------------------------
-- Promotion conditions for a genuinely universal educational assertion.
-- These are DASHI audit obligations, not claims that the Brown papers demand
-- one specific national policy process.
------------------------------------------------------------------------

record UniversalEducationPromotionReceipt : Set where
  constructor universalEducationPromotionReceipt
  field
    targetPopulationTransportReceipt : Set
    targetContextTransportReceipt : Set
    observerCoverageReceipt : Set
    participantRoleReceipt : Set
    localChoiceOrImplementationReceipt : Set
    constitutiveContextReceipt : Set
    contestabilityReceipt : Set

open UniversalEducationPromotionReceipt public

record BrownInformedUniversalPromotionBoundary : Set where
  constructor brownInformedUniversalPromotionBoundary
  field
    variedContextsAutomaticallySupplyObserverCoverage : Bool
    manyParticipantsAutomaticallySupplyStudentAgency : Bool
    identifiedSupportsAutomaticallySupplyUniversalPrescription : Bool
    researcherPerspectiveAutomaticallySuppliesLearnerPerspective : Bool
    conditionalPracticeAutomaticallySuppliesContextFreeEffect : Bool
    universalClaimNeedsTransportAndSituatedReceipts : Bool
    brownCorpusItselfDisprovesUniversalAEROClaim : Bool

canonicalBrownInformedUniversalPromotionBoundary :
  BrownInformedUniversalPromotionBoundary
canonicalBrownInformedUniversalPromotionBoundary =
  brownInformedUniversalPromotionBoundary
    false
    false
    false
    false
    false
    true
    false

------------------------------------------------------------------------
-- Commission-facing reading.
------------------------------------------------------------------------

record CommissionSituatedEvidenceRequirement : Set where
  constructor commissionSituatedEvidenceRequirement
  field
    claimScopeVisible : Bool
    representedObserversVisible : Bool
    absentObserversVisible : Bool
    participantEpistemicRoleVisible : Bool
    localChoiceConditionsVisible : Bool
    constitutiveContextVisible : Bool
    feedbackContestabilityVisible : Bool
    universalPromotionRequiresAdditionalReceipt : Bool

canonicalCommissionSituatedEvidenceRequirement :
  CommissionSituatedEvidenceRequirement
canonicalCommissionSituatedEvidenceRequirement =
  commissionSituatedEvidenceRequirement
    true true true true true true true true

record ACPUEAEROAliceBrownTransportBoundary : Set where
  constructor acpueAeroAliceBrownTransportBoundary
  field
    brownCorpusUsedAsDirectContradictionOfAERO : Bool
    brownCorpusUsedAsAuditRegressionSurface : Bool
    broadEvidenceEqualsUniversalSituatedCoverage : Bool
    universalTransportMayLeaveObserverResidual : Bool
    universalTransportMayLeaveAgencyResidual : Bool
    universalTransportMayLeaveChoiceResidual : Bool
    universalTransportMayLeaveContextResidual : Bool
    universalTransportMayLeaveContestabilityResidual : Bool

canonicalACPUEAEROAliceBrownTransportBoundary :
  ACPUEAEROAliceBrownTransportBoundary
canonicalACPUEAEROAliceBrownTransportBoundary =
  acpueAeroAliceBrownTransportBoundary
    false true false true true true true true
