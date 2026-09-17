module DASHI.Education.DigitalESDIntersectionalSourceAcquisitionParetoRound7Exact where

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
-- ROUND 7: CLASSIFICATION ERROR / HUMAN-CENTRED ABSENCE / DATA AGENCY.
--
-- This round is justified by direct residuals exposed after Round 6:
--   * what real student circumstances exceed a predictive risk model;
--   * whether people affected by algorithms are present in their design;
--   * whether technical dashboard access yields situated data agency.
------------------------------------------------------------------------

data Round7Residual : Set where
  predictionErrorByUncapturedSituatedFactors : Round7Residual
  algorithmDesignByHumanCentredAbsence : Round7Residual
  analyticsAccessByStudentDataAgency : Round7Residual

record Round7Candidate : Set where
  constructor round7-candidate
  field
    source : Attr.AttributedSource
    sourceRoleReceipt : Snowball.SourceRoleSnowballReceipt source
    qidDemand : Identity.ExternalIdentityDemand
    externalIdentityState : String
    deweyState : String
    targetResidual : Round7Residual
    auditLens : PhilosophyAudit.PhilosophyAuditFamily
    sourceBoundedReading : String
    limitation : String
    includedInFinalCorpus : Bool
    includedInFinalCorpusIsFalse : includedInFinalCorpus ≡ false

open Round7Candidate public

mkRound7Candidate :
  (source : Attr.AttributedSource) →
  String →
  Round7Residual →
  PhilosophyAudit.PhilosophyAuditFamily →
  String →
  String →
  Round7Candidate
mkRound7Candidate source identities residual audit reading limitation =
  round7-candidate
    source
    (Snowball.canonicalSourceRoleSnowballReceipt source)
    (Identity.mkOptionalIdentityDemand
      "DigitalESDIntersectionalSourceAcquisitionParetoRound7Exact"
      (Attr.sourceTitle source)
      (Attr.sourceTitle source)
      Identity.wikidataQid
      (Identity.unresolved "no independently verified same-object article QID recorded by round 7"))
    identities
    "Dewey classification unresolved; no nearest-label substitution"
    residual
    audit
    reading
    limitation
    false refl

------------------------------------------------------------------------
-- False-positive / false-negative predictions explained by student interviews.
------------------------------------------------------------------------

hlostaPapathomaHerodotouSource : Attr.AttributedSource
hlostaPapathomaHerodotouSource = Attr.mkDOISource
  "Martin Hlosta; Tina Papathoma; Christothea Herodotou"
  "Explaining Errors in Predictions of At-Risk Students in Distance Learning Education"
  "Artificial Intelligence in Education, LNCS 12164, 119-123"
  "2020"
  "10.1007/978-3-030-52240-7_22"
  "https://doi.org/10.1007/978-3-030-52240-7_22"
  Attr.academicChapterSource
  "Mixed-method error analysis following large-scale predictive learning analytics: interviews with 12 undergraduate distance learners whose assignment-submission outcomes differed from predictions, separating false positives and false negatives. The interview explanations included personal, financial, technical and practical circumstances not represented in the captured model data."
  Attr.publicAttribution

hlostaCandidate : Round7Candidate
hlostaCandidate = mkRound7Candidate
  hlostaPapathomaHerodotouSource
  "DOI verified; PMCID PMC7334695 verified for the open-access chapter representation; article-level QID unresolved"
  predictionErrorByUncapturedSituatedFactors
  PhilosophyAudit.philosophyClaimProvenancePromotion
  "Exceptionally strong 'what exceeds the chart' candidate: prediction errors are investigated by returning to the situated students rather than treating model residuals as unexplained noise. Same prediction carrier can therefore fail to recover financial, personal, technical and practical context relevant to the outcome."
  "Twelve interviewed students in a distance-learning setting and assignment-submission prediction task; does not establish all predictive errors, causal effects of any one omitted factor, or that collecting more personal data is the appropriate remedy."

------------------------------------------------------------------------
-- Human-centred absence in higher-education algorithm design.
------------------------------------------------------------------------

mcConveyGuhaKuzminykhSource : Attr.AttributedSource
mcConveyGuhaKuzminykhSource = Attr.mkDOISource
  "Kelly McConvey; Shion Guha; Anastasia Kuzminykh"
  "A Human-Centered Review of Algorithms in Decision-Making in Higher Education"
  "Proceedings of the 2023 CHI Conference on Human Factors in Computing Systems"
  "2023"
  "10.1145/3544548.3580658"
  "https://doi.org/10.1145/3544548.3580658"
  Attr.academicArticleSource
  "Review of 62 higher-education algorithm-design papers from 2010-2022, coding input data, methods, target outcomes and human-centred approaches. Reports growing use of student personal/protected attributes and increasingly opaque methods while participatory/theoretical/speculative human-centred lenses remain uncommon."
  Attr.publicAttribution

mcConveyCandidate : Round7Candidate
mcConveyCandidate = mkRound7Candidate
  mcConveyGuhaKuzminykhSource
  "DOI and arXiv:2302.05839 verified as distinct publication/preprint identities; QID unresolved"
  algorithmDesignByHumanCentredAbsence
  PhilosophyAudit.feministSubjectPositionProbe
  "High-alpha 'who is not at the design table?' source: the reviewed algorithm literature increasingly represents protected/personal attributes while affected stakeholder perspectives are comparatively absent from design and value assessment."
  "Review of proposed higher-education algorithms, not proof that every deployed system lacks human-centred design or produces harm; presence of protected attributes is not itself evidence of discriminatory treatment."

------------------------------------------------------------------------
-- Technical availability/access versus learner-recognised data agency.
------------------------------------------------------------------------

lluchMolinsLindinSorianoSource : Attr.AttributedSource
lluchMolinsLindinSorianoSource = Attr.mkDOISource
  "Laia Lluch Molins; Carles Lindín Soriano"
  "The self-regulatory paradox of learning analytics: student expectations and the conditions for fair algorithmic assessment in higher education"
  "Frontiers in Education 11, 1913278"
  "2026"
  "10.3389/feduc.2026.1913278"
  "https://doi.org/10.3389/feduc.2026.1913278"
  Attr.academicArticleSource
  "Study of 1,020 undergraduate students at a Spanish research university using the Student Expectations of Learning Analytics Questionnaire. It reports stronger instructor/institution-oriented expectations than student-directed enactment and small gender differences, and interprets data-informed learner agency as a condition that cannot simply be presumed from technical access."
  Attr.publicAttribution

lluchCandidate : Round7Candidate
lluchCandidate = mkRound7Candidate
  lluchMolinsLindinSorianoSource
  "DOI verified; article-level QID unresolved"
  analyticsAccessByStudentDataAgency
  PhilosophyAudit.antiPanopticonVisibilityAuthority
  "Direct discriminator for accessibility/availability x participant agency: a learner may technically receive analytics while not recognising or exercising an entitlement to interpret and act upon those data."
  "Single Spanish university and student-expectation instrument; expectations do not establish realised decision authority, fairness of a named algorithm, longitudinal behaviour change or causal gender mechanisms."

canonicalRound7Frontier : List Round7Candidate
canonicalRound7Frontier =
  hlostaCandidate
  ∷ mcConveyCandidate
  ∷ lluchCandidate
  ∷ []

------------------------------------------------------------------------
-- No-promotion / contestability firewalls.
------------------------------------------------------------------------

data Round7CandidateCreatesIncludedStudy : Set where
data PredictionErrorCreatesStudentDeficitFact : Set where
data ErrorExplanationCreatesMoreDataCollectionMandate : Set where
data HumanCentredReviewCreatesNamedSystemHarm : Set where
data TechnicalAccessibilityCreatesDataAgency : Set where
data StudentExpectationCreatesDecisionAuthority : Set where

round7CandidateDoesNotCreateIncludedStudy : Round7CandidateCreatesIncludedStudy → ⊥
round7CandidateDoesNotCreateIncludedStudy ()

predictionErrorDoesNotCreateStudentDeficitFact :
  PredictionErrorCreatesStudentDeficitFact → ⊥
predictionErrorDoesNotCreateStudentDeficitFact ()

errorExplanationDoesNotCreateMoreDataCollectionMandate :
  ErrorExplanationCreatesMoreDataCollectionMandate → ⊥
errorExplanationDoesNotCreateMoreDataCollectionMandate ()

humanCentredReviewDoesNotCreateNamedSystemHarm :
  HumanCentredReviewCreatesNamedSystemHarm → ⊥
humanCentredReviewDoesNotCreateNamedSystemHarm ()

technicalAccessibilityDoesNotCreateDataAgency :
  TechnicalAccessibilityCreatesDataAgency → ⊥
technicalAccessibilityDoesNotCreateDataAgency ()

studentExpectationDoesNotCreateDecisionAuthority :
  StudentExpectationCreatesDecisionAuthority → ⊥
studentExpectationDoesNotCreateDecisionAuthority ()
