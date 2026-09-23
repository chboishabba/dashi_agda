module DASHI.Education.DigitalESDIntersectionalSourceAcquisitionParetoRound10Exact where

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
-- ROUND 10: CONTESTABILITY / FUTURE OPTIONS / DATA REPURPOSING / LABEL AUTHORITY.
--
-- The Round-9-updated Python absence matrix keeps future options, exclusion by
-- design, category definition and eligible-but-missing parties on the sparse
-- frontier. This round therefore combines three observer positions that must
-- not be collapsed:
--   * affected students speaking about structural grading inequality;
--   * comparative policy history of appeal/protest/reversal;
--   * institutional learning-analytics implementation where enrolment data are
--     repurposed and academics attach risk labels.
--
-- Candidate acquisition != review inclusion and one observer cannot manufacture
-- another observer's authority.
------------------------------------------------------------------------

data Round10Residual : Set where
  studentSituatedGradeAuthorityInequality : Round10Residual
  algorithmicGradeContestabilityAndReversal : Round10Residual
  analyticsDataRepurposingAndRiskLabelAuthority : Round10Residual

record Round10Candidate : Set where
  constructor round10-candidate
  field
    source : Attr.AttributedSource
    sourceRoleReceipt : Snowball.SourceRoleSnowballReceipt source
    qidDemand : Identity.ExternalIdentityDemand
    targetResidual : Round10Residual
    auditLens : PhilosophyAudit.PhilosophyAuditFamily
    sourceBoundedReading : String
    limitation : String
    includedInFinalCorpus : Bool
    includedInFinalCorpusIsFalse : includedInFinalCorpus ≡ false

open Round10Candidate public

mkRound10Candidate :
  (source : Attr.AttributedSource) →
  Round10Residual →
  PhilosophyAudit.PhilosophyAuditFamily →
  String →
  String →
  Round10Candidate
mkRound10Candidate source residual lens reading limitation =
  round10-candidate
    source
    (Snowball.canonicalSourceRoleSnowballReceipt source)
    (Identity.mkOptionalIdentityDemand
      "DigitalESDIntersectionalSourceAcquisitionParetoRound10Exact"
      (Attr.sourceTitle source)
      (Attr.sourceTitle source)
      Identity.wikidataQid
      (Identity.unresolved "no independently verified same-object article QID recorded by round 10"))
    residual lens reading limitation false refl

------------------------------------------------------------------------
-- Student observer: race/class/gender/school-type awareness of grading power.
------------------------------------------------------------------------

bhopalMyersSource : Attr.AttributedSource
bhopalMyersSource = Attr.mkDOISource
  "Kalwant Bhopal; Martin Myers"
  "The impact of COVID-19 on A Level exams in England: Students as consumers"
  "British Educational Research Journal 49(1), 142-157"
  "2023 issue / 2022 online"
  "10.1002/berj.3834"
  "https://doi.org/10.1002/berj.3834"
  Attr.academicArticleSource
  "Peer-reviewed qualitative analysis based on 53 Skype interviews with A-Level students drawn from a wider 583-student project. The interview sample spans gender, multiple ethnic identities and state/independent school types. Students discussed teacher-assessed grades, structural inequality, race/class/gender bias concerns and consequences for university progression."
  Attr.publicAttribution

bhopalMyersCandidate : Round10Candidate
bhopalMyersCandidate = mkRound10Candidate
  bhopalMyersSource
  studentSituatedGradeAuthorityInequality
  PhilosophyAudit.philosophyClaimProvenancePromotion
  "Direct student-observer evidence for who experiences and interprets a high-stakes classification regime, with race/class/gender/school-type structure retained rather than flattened into a generic student-satisfaction score. It gives the hyperfabric participant testimony that the policy-history source cannot create."
  "The interviews principally capture expectations, perceptions and structural-inequality concerns around the 2020 grading process; student testimony does not by itself establish the causal effect of the later standardisation algorithm or the success of any individual appeal."

------------------------------------------------------------------------
-- Policy/history observer: actual appeal/protest/legal contest -> system repeal.
------------------------------------------------------------------------

kellyCalculatedGradesSource : Attr.AttributedSource
kellyCalculatedGradesSource = Attr.mkDOISource
  "Anthony Kelly"
  "A tale of two algorithms: The appeal and repeal of calculated grades systems in England and Ireland in 2020"
  "British Educational Research Journal 47(3), 725-741"
  "2021"
  "10.1002/berj.3705"
  "https://doi.org/10.1002/berj.3705"
  Attr.academicArticleSource
  "Comparative policy analysis of England and Ireland's 2020 calculated-grades systems. It follows design choices, differential consequences, appeal/protest/legal contestation and subsequent policy changes. In England the calculated-grade regime was abandoned and centre-assessed grades substituted after results and public contestation; university progression was a central future-option stake."
  Attr.publicAttribution

kellyCandidate : Round10Candidate
kellyCandidate = mkRound10Candidate
  kellyCalculatedGradesSource
  algorithmicGradeContestabilityAndReversal
  PhilosophyAudit.platformInstitutionalPower
  "Rare acquisition source where contestability is not only normative: collective appeals, protest and legal/political challenge are part of the observed historical chain and are followed by system-level reversal. This directly pays the sparse future-options/decision-authority fibre while keeping policy-history authority distinct from student lived experience."
  "Historical comparative policy analysis, not an individual-level appeal cohort. System repeal does not prove that every harmed student recovered the same university place, timing or future option, and contested interpretations of subgroup bias must remain attributed to their evidential sources."

------------------------------------------------------------------------
-- Institutional observer: enrolled data -> repurposing -> student risk labels.
------------------------------------------------------------------------

lawsonBeerRossiMooreSource : Attr.AttributedSource
lawsonBeerRossiMooreSource = Attr.mkDOISource
  "Celeste Lawson; Colin Beer; Dolene Rossi; Teresa Moore"
  "Identification of 'at risk' students using learning analytics: the ethical dilemmas of intervention strategies in a higher education institution"
  "Educational Technology Research and Development 64(5), 957-968"
  "2016"
  "10.1007/s11423-016-9459-0"
  "https://doi.org/10.1007/s11423-016-9459-0"
  Attr.academicArticleSource
  "Australian institutional case study of a regional university learning-analytics implementation. The authors report an institutional assumption that data consensually gathered at enrolment could be analysed beyond the original consent scope, and that academics used individualized analytics to label students according to estimated success, including uses not intended by the system designers."
  Attr.publicAttribution

lawsonCandidate : Round10Candidate
lawsonCandidate = mkRound10Candidate
  lawsonBeerRossiMooreSource
  analyticsDataRepurposingAndRiskLabelAuthority
  PhilosophyAudit.foucaultSubjectificationDisciplinePower
  "High-alpha category-definition/data-repurposing source: the same enrolled-student data object crosses from collection into a new analytics purpose, while academics become downstream interpreters/classifiers attaching individualized risk meanings. This directly sharpens who defines categories, who interprets evidence and whether original consent survives purpose change."
  "Institutional case-study evidence does not create first-person student authority, prove a legal consent violation, show every label was inaccurate, or establish a universal causal effect of risk labelling."

canonicalRound10Frontier : List Round10Candidate
canonicalRound10Frontier =
  bhopalMyersCandidate
  ∷ kellyCandidate
  ∷ lawsonCandidate
  ∷ []

------------------------------------------------------------------------
-- No-promotion / observer and contestability firewalls.
------------------------------------------------------------------------

data Round10CandidateCreatesIncludedStudy : Set where
data StudentConcernCreatesPolicyOutcome : Set where
data SystemReversalCreatesIndividualAppealSuccess : Set where
data EnrolmentConsentCreatesDownstreamAnalyticsConsent : Set where
data InstitutionalRiskLabelCreatesStudentStateTruth : Set where

round10CandidateDoesNotCreateIncludedStudy : Round10CandidateCreatesIncludedStudy → ⊥
round10CandidateDoesNotCreateIncludedStudy ()

studentConcernDoesNotCreatePolicyOutcome :
  StudentConcernCreatesPolicyOutcome → ⊥
studentConcernDoesNotCreatePolicyOutcome ()

systemReversalDoesNotCreateIndividualAppealSuccess :
  SystemReversalCreatesIndividualAppealSuccess → ⊥
systemReversalDoesNotCreateIndividualAppealSuccess ()

enrolmentConsentDoesNotCreateDownstreamAnalyticsConsent :
  EnrolmentConsentCreatesDownstreamAnalyticsConsent → ⊥
enrolmentConsentDoesNotCreateDownstreamAnalyticsConsent ()

institutionalRiskLabelDoesNotCreateStudentStateTruth :
  InstitutionalRiskLabelCreatesStudentStateTruth → ⊥
institutionalRiskLabelDoesNotCreateStudentStateTruth ()
