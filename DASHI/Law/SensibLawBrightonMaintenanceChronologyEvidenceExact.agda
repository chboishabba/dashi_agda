module DASHI.Law.SensibLawBrightonMaintenanceChronologyEvidenceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- BRIGHTON MAINTENANCE CHRONOLOGY: PRIVATE SOURCE RECEIPT BOUNDARY
--
-- Source corpus reviewed from the tenant's connected Gmail account:
--
--   2 Dec 2022:
--     tenant sends dated photographs and reports extensive condition concerns.
--
--   5 Dec 2022:
--     managing agent says photographs were forwarded to owner and a mould
--     contractor was being arranged.  A separate same-day maintenance notice
--     identifies Job #13812 as "Urgent mould" and states that, FOLLOWING OWNER
--     APPROVAL, the work had been assigned to NATURAL MOULD REMOVAL.
--
--   20 Jan 2023:
--     tenant refers to Job #13812, a second quote, and a 15 Dec follow-up.  In
--     the same thread the managing agent independently apologises for the delay,
--     says she is not having much luck contacting the owner, sends another
--     urgent follow-up, and offers to discuss mutual termination.
--
-- These are distinct approval states.  Initial owner approval for assigning
-- Job #13812 was already present on 5 Dec; the 20 Jan correspondence concerns a
-- later owner response/decision after inspection/quote activity.  This module
-- must not collapse those into "no owner approval until 20 Jan".
--
--   24 Jan 2023:
--     managing agent states the returning mould appears to be a larger issue
--     requiring extensive attention and issues a Form 12 on non-liveability.
--
-- This file intentionally records only the narrow factual chronology supported
-- by those private carriers.  It does NOT publish raw private correspondence,
-- decide causation, decide objective unfitness, or conclude that s 185 was
-- breached.
------------------------------------------------------------------------

record BrightonMaintenanceChronologyEvidence : Set where
  constructor brighton-maintenance-chronology-evidence
  field
    samePremisesPinned : Bool
    decemberConditionReported : Bool
    agentArrangedMouldQuote : Bool
    agentCharacterisedMatterUrgent : Bool
    job13812UrgentMouldPinned : Bool
    initialOwnerApprovalForJob13812Pinned : Bool
    job13812AssignedToNaturalMouldRemoval : Bool
    secondQuoteReferencedBy20January : Bool
    agentAcknowledgedDelay20January : Bool
    laterOwnerResponseStillPending20January : Bool
    urgentFollowupStillRequired20January : Bool
    remediationCompletionNotEstablishedBy20January : Bool
    largerIssueExtensiveAttentionRecognised24January : Bool
    narrowOutstandingRemediationCoordinatePaid : Bool
    statutoryS185FailurePaid : Bool
    wholeS185ViolationPaid : Bool
    privateRawCarrierPublished : Bool
    sourceBoundaryReference : String

canonicalBrightonMaintenanceChronologyEvidence : BrightonMaintenanceChronologyEvidence
canonicalBrightonMaintenanceChronologyEvidence =
  brighton-maintenance-chronology-evidence
    true  -- same premises
    true  -- December condition report
    true  -- quote/inspection workflow arranged
    true  -- urgent characterisation
    true  -- Job #13812 = Urgent mould
    true  -- initial owner approval explicitly recorded on 5 Dec
    true  -- assigned to Natural Mould Removal
    true  -- second quote referenced in 20 Jan thread
    true  -- agent apologises for delay
    true  -- later owner response/decision still being pursued
    true  -- another urgent follow-up sent
    true  -- completed remediation not established in reviewed thread
    true  -- larger issue/extensive attention on 24 Jan
    true  -- narrow outstanding-remediation coordinate
    false -- statutory failure not auto-promoted
    false -- whole violation not auto-promoted
    false -- raw private carriers not published
    "private Gmail receipts: 2022-12-05 Job #13812 assignment after initial owner approval; 2023-01-20 later owner-response delay; 2023-01-24 non-liveability response"

------------------------------------------------------------------------
-- FIREWALLS
------------------------------------------------------------------------

data InitialApprovalEqualsCompletedRemediation : Set where
data LaterOwnerDelayNegatesInitialApproval : Set where
data OutstandingRemediationAutomaticallyEqualsS185Breach : Set where
data AgentDelayAcknowledgementAutomaticallyEqualsNegligence : Set where
data NonLiveabilityAutomaticallyEqualsMaintenanceBreach : Set where

initialApprovalDoesNotEqualCompletedRemediation :
  InitialApprovalEqualsCompletedRemediation → ⊥
initialApprovalDoesNotEqualCompletedRemediation ()

laterOwnerDelayDoesNotNegateInitialApproval :
  LaterOwnerDelayNegatesInitialApproval → ⊥
laterOwnerDelayDoesNotNegateInitialApproval ()

outstandingRemediationDoesNotAutoEqualS185Breach :
  OutstandingRemediationAutomaticallyEqualsS185Breach → ⊥
outstandingRemediationDoesNotAutoEqualS185Breach ()

agentDelayDoesNotAutoEqualNegligence :
  AgentDelayAcknowledgementAutomaticallyEqualsNegligence → ⊥
agentDelayDoesNotAutoEqualNegligence ()

nonLiveabilityDoesNotAutoEqualMaintenanceBreach :
  NonLiveabilityAutomaticallyEqualsMaintenanceBreach → ⊥
nonLiveabilityDoesNotAutoEqualMaintenanceBreach ()
