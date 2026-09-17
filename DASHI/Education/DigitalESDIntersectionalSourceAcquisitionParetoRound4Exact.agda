module DASHI.Education.DigitalESDIntersectionalSourceAcquisitionParetoRound4Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity

------------------------------------------------------------------------
-- ROUND 4: PARTICIPANT VOICE / PRIVACY / AI-ANALYTICS GOVERNANCE.
--
-- This round distinguishes three increasingly participatory source roles:
--   * students describe privacy/consent/trust expectations;
--   * students and teachers co-design an AI-powered analytics artefact;
--   * students co-author policy recommendations in a facilitated workshop.
--
-- None of those labels automatically establishes equal decision authority,
-- institutional adoption, policy effect or durable governance.
------------------------------------------------------------------------

data Round4Residual : Set where
  learningAnalyticsPrivacyByStudentVoice : Round4Residual
  aiAnalyticsCoDesignByStakeholderTension : Round4Residual
  aiPolicyByStudentParticipatoryGovernance : Round4Residual

record Round4Candidate : Set where
  constructor round4-candidate
  field
    source : Attr.AttributedSource
    sourceRoleReceipt : Snowball.SourceRoleSnowballReceipt source
    qidDemand : Identity.ExternalIdentityDemand
    externalIdentityState : String
    deweyState : String
    targetResidual : Round4Residual
    participantRoleReading : String
    sourceBoundedReading : String
    limitation : String
    includedInFinalCorpus : Bool
    includedInFinalCorpusIsFalse : includedInFinalCorpus ≡ false

open Round4Candidate public

mkRound4Candidate :
  (source : Attr.AttributedSource) →
  String →
  Round4Residual →
  String →
  String →
  String →
  Round4Candidate
mkRound4Candidate source identities residual role reading limitation =
  round4-candidate
    source
    (Snowball.canonicalSourceRoleSnowballReceipt source)
    (Identity.mkOptionalIdentityDemand
      "DigitalESDIntersectionalSourceAcquisitionParetoRound4Exact"
      (Attr.sourceTitle source)
      (Attr.sourceTitle source)
      Identity.wikidataQid
      (Identity.unresolved "no independently verified same-object article QID recorded by round 4"))
    identities
    "Dewey classification unresolved; no nearest-label substitution"
    residual
    role
    reading
    limitation
    false refl

------------------------------------------------------------------------
-- Student privacy perspective / informed-consent residual.
------------------------------------------------------------------------

jonesEtAlPrivacySource : Attr.AttributedSource
jonesEtAlPrivacySource = Attr.mkDOISource
  "Kyle M. L. Jones; A. Asher; A. Goben; M. R. Perry; D. Salo; K. A. Briney; M. B. Robertshaw"
  "We're being tracked at all times: Student perspectives of their privacy in relation to learning analytics in higher education"
  "Journal of the Association for Information Science and Technology 71, 1044-1059"
  "2020"
  "10.1002/asi.24358"
  "https://doi.org/10.1002/asi.24358"
  Attr.academicArticleSource
  "Interview study with more than 100 undergraduate students at eight US higher-education institutions examining awareness of learning analytics, privacy, data sharing, informed consent and institutional trust."
  Attr.publicAttribution

jonesCandidate : Round4Candidate
jonesCandidate = mkRound4Candidate
  jonesEtAlPrivacySource
  "DOI verified; PMID/PMCID not recorded/applicable in this acquisition pass"
  learningAnalyticsPrivacyByStudentVoice
  "Direct student interview perspective on privacy, consent, trust and preferred data-sharing boundaries; perspective does not itself prove institutional decision authority."
  "High-alpha source for participant voice x data-governance/privacy and the distinction between analytics capability and informed student participation."
  "US higher-education interview study; does not establish prevalence, legal compliance or adoption of student-preferred governance."

------------------------------------------------------------------------
-- Student + teacher co-design of AI-powered learning analytics.
------------------------------------------------------------------------

alfredoEtAlCoDesignSource : Attr.AttributedSource
alfredoEtAlCoDesignSource = Attr.mkDOISource
  "Riordan Alfredo; Mikaela Milesi; Vanessa Echeverria; Dragan Gasevic; Simon Buckingham Shum; Lin Zhao; Lixiang Yan; Yizhou Jin; J. X. Fan; Viktoria Pammer-Schindler; Zachary Swiecki; Roberto Martinez-Maldonado"
  "Co-designing AI-powered learning analytics: bringing students and teachers together"
  "International Journal of Educational Technology in Higher Education 22, article 78"
  "2025"
  "10.1186/s41239-025-00572-8"
  "https://doi.org/10.1186/s41239-025-00572-8"
  Attr.academicArticleSource
  "Co-design study bringing students and teachers together around AI-powered learning analytics; reports design tensions including teaching-learning goals, privacy-utility and human-AI guidance preferences."
  Attr.publicAttribution

alfredoCandidate : Round4Candidate
alfredoCandidate = mkRound4Candidate
  alfredoEtAlCoDesignSource
  "DOI verified; article-level QID unresolved"
  aiAnalyticsCoDesignByStakeholderTension
  "Students and teachers participate in collaborative design. Co-design is retained as the source-reported participation structure rather than promoted into equal authority or institutional governance control."
  "Direct candidate for participant voice/authority x AI governance x privacy-utility tension while preserving distinct student and teacher observer positions."
  "Co-design process does not prove resulting analytics are deployed, effective, equitable, accessible or institutionally adopted."

------------------------------------------------------------------------
-- Student-driven policy recommendations.
------------------------------------------------------------------------

sekiVijayKotturiSource : Attr.AttributedSource
sekiVijayKotturiSource = Attr.mkDOISource
  "Kaoru Seki; Manisha Vijay; Yasmine Kotturi"
  "Participatory, not Punitive: Student-Driven AI Policy Recommendations in a Design Classroom"
  "Proceedings of the 2026 CHI Conference on Human Factors in Computing Systems"
  "2026"
  "10.1145/3772318.3790691"
  "https://doi.org/10.1145/3772318.3790691"
  Attr.academicArticleSource
  "Participatory workshop study in a graduate design course at a US minority-serving university. Two student leaders facilitated discussions without faculty present; eight participants co-authored ten AI policy recommendations and communicated them in a campus-circulated zine."
  Attr.publicAttribution

sekiCandidate : Round4Candidate
sekiCandidate = mkRound4Candidate
  sekiVijayKotturiSource
  "DOI verified; arXiv 2604.10851 retained as distinct preprint identity; article-level QID unresolved"
  aiPolicyByStudentParticipatoryGovernance
  "Student-led facilitation and co-authored recommendations are retained as stronger participatory evidence than a perception survey, while still remaining distinct from final institutional decision authority."
  "Direct candidate for the audit distinction participation/voice x policy authorship x institutional authority."
  "Eight participants in one design-classroom workshop series; co-authored recommendations do not establish institutional adoption, equal governance power or policy outcomes."

canonicalRound4Frontier : List Round4Candidate
canonicalRound4Frontier =
  jonesCandidate
  ∷ alfredoCandidate
  ∷ sekiCandidate
  ∷ []

------------------------------------------------------------------------
-- Authority / observer firewalls.
------------------------------------------------------------------------

data Round4CandidateCreatesIncludedStudy : Set where
data StudentPerspectiveCreatesDecisionAuthority : Set where
data CoDesignCreatesEqualDecisionAuthority : Set where
data PolicyRecommendationCreatesInstitutionalPolicy : Set where
data StudentVoiceCreatesGovernanceOutcome : Set where

round4CandidateDoesNotCreateIncludedStudy : Round4CandidateCreatesIncludedStudy → ⊥
round4CandidateDoesNotCreateIncludedStudy ()

studentPerspectiveDoesNotCreateDecisionAuthority :
  StudentPerspectiveCreatesDecisionAuthority → ⊥
studentPerspectiveDoesNotCreateDecisionAuthority ()

coDesignDoesNotCreateEqualDecisionAuthority :
  CoDesignCreatesEqualDecisionAuthority → ⊥
coDesignDoesNotCreateEqualDecisionAuthority ()

policyRecommendationDoesNotCreateInstitutionalPolicy :
  PolicyRecommendationCreatesInstitutionalPolicy → ⊥
policyRecommendationDoesNotCreateInstitutionalPolicy ()

studentVoiceDoesNotCreateGovernanceOutcome :
  StudentVoiceCreatesGovernanceOutcome → ⊥
studentVoiceDoesNotCreateGovernanceOutcome ()
