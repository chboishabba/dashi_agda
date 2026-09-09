module DASHI.Law.SensibLawBrightonMaintenanceChronologyEvidenceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- BRIGHTON MAINTENANCE CHRONOLOGY: PRIVATE SOURCE RECEIPT BOUNDARY
--
-- Source corpus reviewed from the tenant's connected Gmail account:
--
--   2 Dec 2022:
--     tenant sends dated photographs and reports extensive condition concerns.
--
--   5 Dec 2022:
--     managing agent says photographs were forwarded to owner, a mould company
--     was arranged to quote, work approval would be sought while contractor was
--     onsite, and the matter was being treated as urgent.
--
--   20 Jan 2023:
--     tenant refers to urgent maintenance order Job #13812 dated 5 Dec and a
--     second quote.  In the same thread the managing agent independently
--     apologises for the delay, says attempts to contact the owner had not been
--     successful, sends another urgent follow-up, and offers to discuss mutual
--     termination while remediation remains pending.
--
--   24 Jan 2023:
--     managing agent states the returning mould appears to be a larger issue
--     requiring extensive attention and issues a Form 12 on non-liveability.
--
-- This file intentionally records only the narrow factual chronology supported
-- by those private carriers.  It does NOT publish raw private correspondence,
-- decide causation, decide reasonableness, or conclude that s 185 was breached.
------------------------------------------------------------------------

record BrightonMaintenanceChronologyEvidence : Set where
  constructor brighton-maintenance-chronology-evidence
  field
    samePremisesPinned : Bool
    decemberConditionReported : Bool
    agentArrangedMouldQuote : Bool
    agentCharacterisedMatterUrgent : Bool
    secondQuoteReferencedBy20January : Bool
    agentAcknowledgedDelay20January : Bool
    ownerApprovalStillPending20January : Bool
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
    true   -- same premises pinned
    true   -- December condition report
    true   -- mould quote arranged
    true   -- agent treated matter as urgent
    true   -- tenant's 20 Jan thread references second quote
    true   -- agent independently apologises for delay
    true   -- owner response/approval still outstanding
    true   -- agent sends another urgent follow-up
    true   -- no completed remediation established by that thread
    true   -- 24 Jan larger/extensive issue recognition
    true   -- narrow factual outstanding-remediation coordinate
    false  -- statutory s 185 failure still needs legal evaluation
    false  -- whole violation not promoted
    false  -- raw private carriers not published here
    "private Gmail source receipts: 2022-12-05 agent response; 2023-01-20 maintenance thread; 2023-01-24 non-liveability response"

------------------------------------------------------------------------
-- FIREWALLS
------------------------------------------------------------------------

data OutstandingRemediationAutomaticallyEqualsS185Breach : Set where
data AgentDelayAcknowledgementAutomaticallyEqualsNegligence : Set where
data NonLiveabilityAutomaticallyEqualsMaintenanceBreach : Set where

outstandingRemediationDoesNotAutoEqualS185Breach :
  OutstandingRemediationAutomaticallyEqualsS185Breach → ⊥
outstandingRemediationDoesNotAutoEqualS185Breach ()

agentDelayDoesNotAutoEqualNegligence :
  AgentDelayAcknowledgementAutomaticallyEqualsNegligence → ⊥
agentDelayDoesNotAutoEqualNegligence ()

nonLiveabilityDoesNotAutoEqualMaintenanceBreach :
  NonLiveabilityAutomaticallyEqualsMaintenanceBreach → ⊥
nonLiveabilityDoesNotAutoEqualMaintenanceBreach ()
