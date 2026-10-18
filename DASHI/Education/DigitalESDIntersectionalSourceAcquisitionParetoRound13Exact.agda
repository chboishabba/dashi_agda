module DASHI.Education.DigitalESDIntersectionalSourceAcquisitionParetoRound13Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Education.DigitalESDPhilosophySurveillanceAuditBoundaryExact as PhilosophyAudit

------------------------------------------------------------------------
-- ROUND 13: ASSESSMENT-DESIGN EXCLUSION / ACTUAL WITHDRAWAL / FAMILY AGENCY.
--
-- Post-Round-12 Python coverage keeps whoWasExcludedByDesign,
-- whoWasEligibleButMissing and whoseFutureOptionsWereAffected on the P0
-- frontier. Round 13 therefore prioritises observed mechanisms that alter the
-- practical educational option set rather than another generic inclusion paper.
------------------------------------------------------------------------

data Round13Residual : Set where
  disabilityAssessmentDesignConstrainsCourseChoice : Round13Residual
  timePovertyObservedWithdrawalFromOpenOnlineHE : Round13Residual
  migrantRefugeeParentDigitalExclusionConstrainsAgency : Round13Residual

record Round13Candidate : Set where
  constructor round13-candidate
  field
    source : Attr.AttributedSource
    sourceRoleReceipt : Snowball.SourceRoleSnowballReceipt source
    qidDemand : Identity.ExternalIdentityDemand
    targetResidual : Round13Residual
    auditLens : PhilosophyAudit.PhilosophyAuditFamily
    sourceBoundedReading : String
    limitation : String
    includedInFinalCorpus : Bool
    includedInFinalCorpusIsFalse : includedInFinalCorpus ≡ false

open Round13Candidate public

mkRound13Candidate :
  (source : Attr.AttributedSource) →
  Round13Residual →
  PhilosophyAudit.PhilosophyAuditFamily →
  String →
  String →
  Round13Candidate
mkRound13Candidate source residual lens reading limitation =
  round13-candidate
    source
    (Snowball.canonicalSourceRoleSnowballReceipt source)
    (Identity.mkOptionalIdentityDemand
      "DigitalESDIntersectionalSourceAcquisitionParetoRound13Exact"
      (Attr.sourceTitle source)
      (Attr.sourceTitle source)
      Identity.wikidataQid
      (Identity.unresolved "no independently verified same-object article QID recorded by round 13"))
    residual lens reading limitation false refl

------------------------------------------------------------------------
-- Disabled students: assessment design changes practical course/exam options.
------------------------------------------------------------------------

taiEtAlExaminationsSource : Attr.AttributedSource
taiEtAlExaminationsSource = Attr.mkDOISource
  "Joanna Tai; Paige Mahoney; Rola Ajjawi; Margaret Bearman; Joanne Dargusch; Mary Dracup; Lois Harris"
  "How are examinations inclusive for students with disabilities in higher education? A sociomaterial analysis"
  "Assessment & Evaluation in Higher Education 48(3), 390-402"
  "2023 issue / 2022 online"
  "10.1080/02602938.2022.2077910"
  "https://doi.org/10.1080/02602938.2022.2077910"
  Attr.academicArticleSource
  "Open-access interview study with 40 disabled students across two Australian universities. Students described avoiding examinations and selecting units whose assessment arrangements aligned better with their strengths. Inclusion/exclusion emerged from combinations of time, technology, equipment, space, staff implementation and assessment flexibility; online/open-book shifts increased inclusion for many but not all."
  Attr.publicAttribution

taiCandidate : Round13Candidate
taiCandidate = mkRound13Candidate
  taiEtAlExaminationsSource
  disabilityAssessmentDesignConstrainsCourseChoice
  PhilosophyAudit.philosophyClaimProvenancePromotion
  "Direct source for assessment-design exclusion x future options: a nominally eligible student can alter unit/exam choices around the assessment carrier, so formal enrolment availability does not determine practical option availability."
  "Forty students registered with disability support services at two Australian universities; findings do not estimate population prevalence or prove all examinations exclude disabled students. Avoiding an assessment format does not establish academic incapacity or lack of subject competence."

------------------------------------------------------------------------
-- Open online HE: actual withdrawal/stopout and time/lifeload constraints.
------------------------------------------------------------------------

xavierMenesesFiuzaSource : Attr.AttributedSource
xavierMenesesFiuzaSource = Attr.mkDOISource
  "Marlon Xavier; Julio Meneses; Patricia Jantsch Fiuza"
  "Dropout, stopout, and time challenges in open online higher education: A qualitative study of the first-year student experience"
  "Open Learning: The Journal of Open, Distance and e-Learning 41(1), 24-40"
  "2026 issue / 2022 online"
  "10.1080/02680513.2022.2160236"
  "https://doi.org/10.1080/02680513.2022.2160236"
  Attr.academicArticleSource
  "Retrospective qualitative study of 16 first-year undergraduate learners who withdrew from an open university. Participants described time poverty and time conflicts involving health, family, work, expectations and study management; stopouts and dropouts differed in whether they could later improve time conditions and re-enrol."
  Attr.publicAttribution

xavierCandidate : Round13Candidate
xavierCandidate = mkRound13Candidate
  xavierMenesesFiuzaSource
  timePovertyObservedWithdrawalFromOpenOnlineHE
  PhilosophyAudit.philosophyClaimProvenancePromotion
  "Direct future-options/eligible-but-missing source: these learners are observed after leaving the active student carrier, so dropout is not inferred from low telemetry. Life/work/family time constraints can remove practical continuation despite formal openness/flexibility."
  "Sixteen retrospective interviewees at one open university; withdrawal is heterogeneous and does not imply low motivation, academic inability or that time poverty is the sole cause of dropout in online HE."

------------------------------------------------------------------------
-- Migrant/refugee family observer: digital/language exclusion reduces agency.
------------------------------------------------------------------------

naidooTanWagnerSource : Attr.AttributedSource
naidooTanWagnerSource = Attr.mkDOISource
  "Loshini Naidoo; Lynde Tan; Sharon Wagner"
  "Relational agency in practice: how migrant and refugee parents navigate digital learning in Western Sydney"
  "International Journal of Inclusive Education"
  "2025"
  "10.1080/13603116.2025.2573826"
  "https://doi.org/10.1080/13603116.2025.2573826"
  Attr.academicArticleSource
  "Peer-reviewed qualitative study using interviews and focus groups with migrant and refugee background parents in Western Sydney. It examines how digital access, language and contextual barriers shape parent-school/community engagement and can reduce parents from active partners to passive recipients in digitally mediated education."
  Attr.publicAttribution

naidooCandidate : Round13Candidate
naidooCandidate = mkRound13Candidate
  naidooTanWagnerSource
  migrantRefugeeParentDigitalExclusionConstrainsAgency
  PhilosophyAudit.philosophyClaimProvenancePromotion
  "Adds a family/community observer that student-only studies cannot manufacture: digital and linguistic access affect who can participate in school relationships, interpret information and exercise relational agency around a child's education."
  "Parent observer does not substitute for child/student voice, and broad migrant/refugee labels must not erase within-group differences. The study does not establish one universal digital-exclusion mechanism or causal educational-outcome effect."

canonicalRound13Frontier : List Round13Candidate
canonicalRound13Frontier =
  taiCandidate
  ∷ xavierCandidate
  ∷ naidooCandidate
  ∷ []

------------------------------------------------------------------------
-- No-promotion / option-set firewalls.
------------------------------------------------------------------------

data Round13CandidateCreatesIncludedStudy : Set where
data AssessmentAvoidanceCreatesAcademicIncapacity : Set where
data WithdrawalCreatesLowMotivation : Set where
data ParentDigitalExclusionCreatesStudentVoice : Set where

round13CandidateDoesNotCreateIncludedStudy : Round13CandidateCreatesIncludedStudy → ⊥
round13CandidateDoesNotCreateIncludedStudy ()

assessmentAvoidanceDoesNotCreateAcademicIncapacity :
  AssessmentAvoidanceCreatesAcademicIncapacity → ⊥
assessmentAvoidanceDoesNotCreateAcademicIncapacity ()

withdrawalDoesNotCreateLowMotivation : WithdrawalCreatesLowMotivation → ⊥
withdrawalDoesNotCreateLowMotivation ()

parentDigitalExclusionDoesNotCreateStudentVoice :
  ParentDigitalExclusionCreatesStudentVoice → ⊥
parentDigitalExclusionDoesNotCreateStudentVoice ()
