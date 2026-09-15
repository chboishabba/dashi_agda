module DASHI.Culture.MissingDeceasedTwentyScientistRound60MPTLECRExternalCitationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Culture.MissingDeceasedTwentyScientistRound53ParetoAcquisitionSchedulerExact as R53
import DASHI.Culture.MissingDeceasedTwentyScientistRound56ProofCarryingSchedulerFeedbackExact as R56
import DASHI.Culture.MissingDeceasedTwentyScientistRound59MPTLAchromatAcquisitionExact as R59
import DASHI.Law.SensibLawAdaptiveLegalResearchFeedbackLoopExact as Feedback
import DASHI.Law.SensibLawProofSearchResultAssessmentExact as Assessment

------------------------------------------------------------------------
-- ROUND 60: MPTL ENGINEERING CAPABILITY REVIEW + EXTERNAL TECHNICAL CITATION
--
-- Two source roles remain separate:
--
-- 1. OSTI/LANL metadata for LA-UR-24-30822:
--      DARHT Multi-Pulse Test Line (MPTL) ECR
--      Aaron Mills Brandes
--      Engineering Capability Review
--      issued 2024-10-07; approved for public release.
--
-- 2. A 2025 technical conference abstract from the Budker Institute / Russian
--    Federal Nuclear Center cites Brandes 2024 as prior work on the multi-pulse
--    beam-target interaction problem.
--
-- This independently corroborates the technical existence/relevance of the ECR
-- carrier. It does not create a cross-person cohort link, a U.S.-Russia programme
-- link, or any causal/targeting inference.
------------------------------------------------------------------------

record MPTLECRReceipt : Set where
  constructor mptl-ecr-receipt
  field
    sourceOwner : String
    nativeLocator : String
    sourceIdentifier : String
    sourceTitle : String
    namedAuthor : String
    authorRoleReference : String
    intendedFor : String
    issueDate : String
    publicReleaseReference : String
    externalCitationReference : String
    externalCitationUseReference : String
    secondRetainedPersonPaid : Bool
    scopeBoundary : String

open MPTLECRReceipt public

mptlECRReceipt : MPTLECRReceipt
mptlECRReceipt = mptl-ecr-receipt
  "Los Alamos National Laboratory / OSTI metadata carrier"
  "https://www.osti.gov/servlets/purl/2460464"
  "LA-UR-24-30822"
  "DARHT Multi-Pulse Test Line (MPTL) ECR"
  "Aaron Mills Brandes"
  "DARHT R&D Engineer / Integrated Weapons Experiments as exposed on the acquired public surface"
  "Engineering Capability Review, Los Alamos, New Mexico"
  "2024-10-07; public surface also carries July-2024 ECR dating"
  "approved for public release; distribution unlimited"
  "2025 Budker Institute / Russian Federal Nuclear Center conference abstract cites Brandes A. M. 2024, DARHT Multi-Pulse Test Line (MPTL) ECR"
  "prior technical work for the multi-pulse linear-induction-accelerator beam-target interaction problem"
  false
  "Pays the existence, identity and public technical reuse of LA-UR-24-30822. It does not identify Alex Press, M. Schulze or Anthony Chavez as ECR authors/participants; it does not prove that the ECR contains the LA-UR-22-21508 achromat revision; and it does not create any personnel, programme, causation or targeting link from the external citation."

mptlECRPublicReleasePaid : Bool
mptlECRPublicReleasePaid = true

mptlECRExternalTechnicalCitationPaid : Bool
mptlECRExternalTechnicalCitationPaid = true

mptlECRSecondRetainedPersonPaid : Bool
mptlECRSecondRetainedPersonPaid = secondRetainedPersonPaid mptlECRReceipt

externalCitationDoesNotPayPersonnelCrossing : Bool
externalCitationDoesNotPayPersonnelCrossing = true

externalCitationDoesNotPaySharedInternationalProgramme : Bool
externalCitationDoesNotPaySharedInternationalProgramme = true

technicalCitationDoesNotTransferSourceAuthority : Bool
technicalCitationDoesNotTransferSourceAuthority = true

------------------------------------------------------------------------
-- Scheduler consequence.
--
-- The ECR changes the live acquisition route because an exact engineering
-- review object now exists.  The next acquisition should target review-support
-- material, attendees/approvers only where publicly identified, drawings and
-- referenced design artefacts rather than generic DARHT biography searches.
------------------------------------------------------------------------

mptlECRAssessment : R56.AcquisitionAssessment
mptlECRAssessment = R56.acquisition-assessment
  R53.chavezScorpiusCrossingTask
  "OSTI/LANL LA-UR-24-30822 + 2025 independent technical citation"
  "An exact public MPTL Engineering Capability Review exists under LA-UR-24-30822, authored by Aaron Mills Brandes, and is independently cited as technical prior work on multi-pulse beam-target interaction"
  "primary-like OSTI/LANL metadata plus independent external technical citation"
  "exact ECR existence/identity/reuse proposition only"
  R56.admittedPayment
  Assessment.frontierNarrowed
  "Round 59: exact 2022 MPTL achromat object by M. Schulze; workshop-to-report/ECR lineage unresolved"
  "Round 60: exact 2024 MPTL ECR carrier and independent technical citation paid; ECR contents/approver/design-artifact lineage and retained crossing remain unresolved"
  "DARHT MPTL ECR / engineering-review / design-artifact provenance neighbourhood"
  "Round 60 real MPTL ECR acquisition assessment"

mptlECRFeedbackRecomputes :
  Feedback.feedbackDisposition
    (R56.outcomePayment (R56.outcome mptlECRAssessment))
    (R56.frontierChange mptlECRAssessment)
  ≡ Feedback.recomputeFrontier
mptlECRFeedbackRecomputes = refl

mptlECRNextResidual : String
mptlECRNextResidual = "Acquire the publicly releasable ECR contents or derivative review/support records for LA-UR-24-30822, then trace exact references to LA-UR-22-21508, Alex Press's MPTL workshop surface, drawings, approvers and named engineering participants. Only an identity-bearing retained-person receipt on the same exact object can pay H2."

round60H2PaidCount : Nat
round60H2PaidCount = 0

round60H3PaidCount : Nat
round60H3PaidCount = 0

round60Reading : String
round60Reading = "The acquisition loop has reached an exact MPTL engineering-review object: LA-UR-24-30822, DARHT Multi-Pulse Test Line (MPTL) ECR, authored by Aaron Mills Brandes and approved for public release. A 2025 Budker Institute / Russian Federal Nuclear Center technical abstract independently cites that ECR as prior work on multi-pulse beam-target interaction. This strengthens carrier identity and technical provenance while leaving personnel crossing unpaid. The scheduler therefore narrows again toward ECR support material, drawings, review participants and explicit cross-references, with H2/H3 unchanged."
