module DASHI.Culture.MissingDeceasedTwentyScientistRound57FirstRealAcquisitionAssessmentExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Culture.MissingDeceasedTwentyScientistRound53ParetoAcquisitionSchedulerExact as R53
import DASHI.Culture.MissingDeceasedTwentyScientistRound56ProofCarryingSchedulerFeedbackExact as R56
import DASHI.Law.SensibLawAdaptiveLegalResearchFeedbackLoopExact as Feedback
import DASHI.Law.SensibLawProofSearchResultAssessmentExact as Assessment

------------------------------------------------------------------------
-- ROUND 57: FIRST REAL ACQUISITION ASSESSMENT
--
-- This owner takes an actually acquired public technical source through the
-- Round-56 assessment carrier.  It is deliberately proposition-scoped:
--
--   paid: Anthony/Mark Anthony Chavez appears on LA-UR-24-27763, an exact
--         Scorpius + DARHT Multi-Pulse Test Line beam-position-monitor report.
--
--   unpaid: another retained scientist appears on that exact report/object.
--
-- The source therefore improves exact-object resolution without paying H2.
------------------------------------------------------------------------

record RealAcquisitionReceipt : Set where
  constructor real-acquisition-receipt
  field
    acquisitionTask : R53.AcquisitionTask
    sourceOwner : String
    sourceKind : String
    nativeLocator : String
    sourceIdentifier : String
    sourceDate : String
    sourceTitle : String
    sourceAuthors : String
    exactPaidProposition : String
    identityWeldReference : String
    boundedNegativeReference : String
    sourceRoleBoundary : String

open RealAcquisitionReceipt public

chavezScorpiusOSTIReceipt : RealAcquisitionReceipt
chavezScorpiusOSTIReceipt = real-acquisition-receipt
  R53.chavezScorpiusCrossingTask
  "U.S. Department of Energy Office of Scientific and Technical Information (OSTI) public report carrier"
  "public technical report / primary-like report carrier"
  "https://www.osti.gov/servlets/purl/2406682"
  "LA-UR-24-27763"
  "2024-07-23"
  "An Improved Beam Position Monitor for Scorpius and the DARHT Multi-Pulse Test Line"
  "Carl August Ekdahl Jr.; Kimberly Lynn Abdallah; William B. Broste; Mark Anthony Chavez; Christopher James Mastrangelo; Matthew Carter Richards"
  "Mark Anthony Chavez is a named author on the exact Scorpius/DARHT Multi-Pulse Test Line beam-position-monitor report LA-UR-24-27763"
  "Round 40 LANL same-person/object context already pays Anthony Chavez -> DARHT career + Scorpius design-work identity/context; Round 57 does not manufacture a new identity rule from name similarity alone"
  "the acquired report author list contains no second retained scientist; this is bounded to this exact report author surface and does not prove absence from the wider Scorpius/DARHT programme"
  "the report pays authorship and exact technical-object participation only; it does not pay a common programme, targeting, causation, or a broader personnel roster"

laUR2427763ExactObjectPaid : Bool
laUR2427763ExactObjectPaid = true

secondRetainedScientistOnLAUR2427763Paid : Bool
secondRetainedScientistOnLAUR2427763Paid = false

boundedAuthorListAbsenceIsNotProgrammeAbsence : Bool
boundedAuthorListAbsenceIsNotProgrammeAbsence = true

exactTechnicalAuthorshipDoesNotPaySharedProgramme : Bool
exactTechnicalAuthorshipDoesNotPaySharedProgramme = true

------------------------------------------------------------------------
-- Secondary institutional context retained as a distinct source role.
-- LANL's 2025 engineering profile says Anthony Chavez started at LANL in 1989,
-- worked at DARHT for more than 25 years, and completed design work for the
-- Scorpius accelerator.  It corroborates identity/object context but is not
-- counted as a second independent proof of the exact LA-UR author proposition.
------------------------------------------------------------------------

lanlProfileLocator : String
lanlProfileLocator = "https://cdn.lanl.gov/files/nss-2025-engineering-online_f0e10.pdf"

lanlProfileRole : String
lanlProfileRole = "LANL institutional profile paying Anthony Chavez DARHT career and Scorpius design-work context"

lanlProfileDoesNotMultiplyExactReportAuthorshipEvidence : Bool
lanlProfileDoesNotMultiplyExactReportAuthorshipEvidence = true

------------------------------------------------------------------------
-- Proof-carrying assessment.
--
-- The proposition itself is admitted.  The H2 crossing residual is not closed,
-- so the scheduler frontier is unchanged for that consumer.  Existing SensibLaw
-- feedback semantics therefore continue the search rather than recomputing a
-- paid/narrowed frontier.
------------------------------------------------------------------------

chavezRealAcquisitionAssessment : R56.AcquisitionAssessment
chavezRealAcquisitionAssessment = R56.acquisition-assessment
  R53.chavezScorpiusCrossingTask
  "OSTI LA-UR-24-27763 public report acquired from native public carrier"
  "Mark Anthony Chavez is a named author on LA-UR-24-27763, an exact Scorpius and DARHT Multi-Pulse Test Line beam-position-monitor report"
  "exact public technical report authorship/object-participation source"
  "Chavez exact engineering-object participation only"
  R56.admittedPayment
  Assessment.frontierUnchanged
  "Scorpius/DARHT H2 residual: locate another retained scientist on the same literal task/drawing/review/work-package/object"
  "same H2 residual remains live; exact Chavez object resolution is stronger"
  "Chavez Scorpius/DARHT exact-object scheduler neighbourhood"
  "Round 57 real acquisition assessment: admitted exact-object proposition, unchanged H2 frontier"

realAcquisitionAdmittedButFrontierUnchanged : Bool
realAcquisitionAdmittedButFrontierUnchanged = true

admittedUnchangedContinuesSearch :
  Feedback.feedbackDisposition
    (R56.outcomePayment (R56.outcome chavezRealAcquisitionAssessment))
    (R56.frontierChange chavezRealAcquisitionAssessment)
  ≡ Feedback.continueSearch
admittedUnchangedContinuesSearch = refl

realAcquisitionKnowledgeGainDoesNotPayH2 : Bool
realAcquisitionKnowledgeGainDoesNotPayH2 = true

frontierUnchangedDoesNotMeanNoKnowledgeGain : Bool
frontierUnchangedDoesNotMeanNoKnowledgeGain = true

------------------------------------------------------------------------
-- Non-progress for one consumer is not source rejection.
--
-- The exact report is useful and admitted for Chavez object resolution.  It is
-- non-progressing only with respect to the *second-retained-person H2 crossing*
-- consumer because none of the other named report authors is in the retained
-- cohort.  That consumer-relative distinction is preserved explicitly.
------------------------------------------------------------------------

record ConsumerRelativeDisposition : Set where
  constructor consumer-relative-disposition
  field
    propositionPaid : Bool
    h2CrossingPaid : Bool
    exactObjectKnowledgeImproved : Bool
    continueAcquisitionSearch : Bool
    dispositionReference : String

open ConsumerRelativeDisposition public

chavezConsumerRelativeDisposition : ConsumerRelativeDisposition
chavezConsumerRelativeDisposition = consumer-relative-disposition
  true false true true
  "admit LA-UR-24-27763 exact-object proposition; retain H2 crossing residual and continue exact engineering-artifact/personnel snowball"

------------------------------------------------------------------------
-- Attribution / scope firewalls.
------------------------------------------------------------------------

reportAuthorshipCannotTransferClaimsFromLANLProfile : Bool
reportAuthorshipCannotTransferClaimsFromLANLProfile = true

lanlProfileCannotTransferClaimsIntoOSTIReport : Bool
lanlProfileCannotTransferClaimsIntoOSTIReport = true

noSecondRetainedAuthorCannotPayUniversalNonParticipation : Bool
noSecondRetainedAuthorCannotPayUniversalNonParticipation = true

oneExactChavezObjectCannotPayCohortCommonProgramme : Bool
oneExactChavezObjectCannotPayCohortCommonProgramme = true

round57H2PaidCount : Nat
round57H2PaidCount = 0

round57H3PaidCount : Nat
round57H3PaidCount = 0

round57Reading : String
round57Reading = "The first real Pareto-scheduled acquisition has passed through the professional assessment carrier. OSTI LA-UR-24-27763 pays a stronger exact proposition: Mark Anthony Chavez is a named author on an improved beam-position-monitor report for Scorpius and the DARHT Multi-Pulse Test Line. The exact report author surface contains no second retained scientist, so the Chavez H2 crossing residual remains live. This is admitted knowledge gain with a consumer-relative unchanged H2 frontier, not source rejection and not promotion. LANL institutional context remains a separate source role and corroborates Chavez's DARHT/Scorpius identity/object context without multiplying the exact report authorship evidence."

round57Next : String
round57Next = "Continue the same Chavez neighbourhood into the report's cited design/test-line artefacts, beam-position-monitor hardware lineage, design reviews and work-package/team records. In parallel, keep the current Pareto frontier intact because this acquisition did not close or reopen H2/H3; each subsequent source must pass the same proposition-level assessment carrier."
