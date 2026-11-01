module DASHI.Biology.HumourOnlineEngagementFramework where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Biology.EducationCorpusSourceRegistry as Sources

------------------------------------------------------------------------
-- SOURCE-BOUND HUMOUR FRAMEWORK
--
-- Bibliographic anchor:
--   Alice Brown, Josephine Pryce, Anja Pabel (2025),
--   "Considerations for integrating humour as a strategy to heighten online
--   student engagement and learning in higher education: An emerging
--   framework", Higher Education Research and Development Society of
--   Australasia (HERDSA) Conference, Perth, p. 64.
--   DOI: no DOI assigned/listed for the conference item.
--
-- Content basis:
--   The seven-consideration surface below is source-bound to the supplied
--   manuscript/draft discussed in the accompanying correspondence.  The
--   bibliographic conference item anchors author/title/venue/year; this module
--   does not promote the richer draft into a peer-reviewed empirical claim.
--
-- Source/DASHI boundary:
--   This file preserves the framework before any later intersectional,
--   epistemic-agency, PNF, hyperfabric, or dynamic-quotient reinterpretation.
------------------------------------------------------------------------

data HumourConsideration : Set where
  rationaleConsideration : HumourConsideration
  presenterConsideration : HumourConsideration
  audienceContextConsideration : HumourConsideration
  contentConsideration : HumourConsideration
  technicalSkillsConsideration : HumourConsideration
  humourTypeConsideration : HumourConsideration
  feedbackConsideration : HumourConsideration

considerationName : HumourConsideration → String
considerationName rationaleConsideration = "rationale"
considerationName presenterConsideration = "presenter disposition and skills"
considerationName audienceContextConsideration = "audience and context"
considerationName contentConsideration = "content"
considerationName technicalSkillsConsideration = "technical skills / delivery"
considerationName humourTypeConsideration = "type of humour"
considerationName feedbackConsideration = "feedback to humour"

canonicalHumourConsiderations : List HumourConsideration
canonicalHumourConsiderations =
  rationaleConsideration
  ∷ presenterConsideration
  ∷ audienceContextConsideration
  ∷ contentConsideration
  ∷ technicalSkillsConsideration
  ∷ humourTypeConsideration
  ∷ feedbackConsideration
  ∷ []

------------------------------------------------------------------------
-- Source-level role orientation.
--
-- These roles describe the grammar of the supplied framework.  They do not
-- claim teacher intent determines student meaning and do not yet import the
-- later Brown/Kimber epistemic-agency correction.
------------------------------------------------------------------------

data FrameworkParticipantRole : Set where
  teacherDesignerRole : FrameworkParticipantRole
  studentAudienceRole : FrameworkParticipantRole
  studentFeedbackRole : FrameworkParticipantRole
  studentHumourContributorRole : FrameworkParticipantRole

primaryRoleAt : HumourConsideration → FrameworkParticipantRole
primaryRoleAt rationaleConsideration = teacherDesignerRole
primaryRoleAt presenterConsideration = teacherDesignerRole
primaryRoleAt audienceContextConsideration = studentAudienceRole
primaryRoleAt contentConsideration = teacherDesignerRole
primaryRoleAt technicalSkillsConsideration = teacherDesignerRole
primaryRoleAt humourTypeConsideration = teacherDesignerRole
primaryRoleAt feedbackConsideration = studentFeedbackRole

record HumourFrameworkSourceSurface : Set where
  constructor humourFrameworkSourceSurface
  field
    sourcePaper : Sources.PaperReference
    sourcePaperIsCanonical : sourcePaper ≡ Sources.humourFrameworkPaper
    considerations : List HumourConsideration
    considerationsAreCanonical : considerations ≡ canonicalHumourConsiderations

    researcherCoConstructionReported : Bool
    researcherCoConstructionReportedIsTrue :
      researcherCoConstructionReported ≡ true

    studentFrameworkCoConstructionReported : Bool
    studentFrameworkCoConstructionReportedIsFalse :
      studentFrameworkCoConstructionReported ≡ false

    futureWorkSeeksStudentPerspectives : Bool
    futureWorkSeeksStudentPerspectivesIsTrue :
      futureWorkSeeksStudentPerspectives ≡ true

    studentHumourContributionMentioned : Bool
    studentHumourContributionMentionedIsTrue :
      studentHumourContributionMentioned ≡ true

    sourceFrameworkClaimsEpistemicAgency : Bool
    sourceFrameworkClaimsEpistemicAgencyIsFalse :
      sourceFrameworkClaimsEpistemicAgency ≡ false

    sourceFrameworkPreservedBeforeLaterCorrection : Bool
    sourceFrameworkPreservedBeforeLaterCorrectionIsTrue :
      sourceFrameworkPreservedBeforeLaterCorrection ≡ true

    reading : String

open HumourFrameworkSourceSurface public

canonicalHumourFrameworkSourceSurface : HumourFrameworkSourceSurface
canonicalHumourFrameworkSourceSurface =
  humourFrameworkSourceSurface
    Sources.humourFrameworkPaper refl
    canonicalHumourConsiderations refl
    true refl
    false refl
    true refl
    true refl
    false refl
    true refl
    "Source-bound emerging framework: researchers co-construct seven practical considerations for online humour; students are primarily modelled as audience and feedback sources, with student humour contribution mentioned and student perspectives proposed as future work. No later epistemic-agency, intersectional-hyperfabric or dynamic-safety claim is retrofitted into the source paper."
