module DASHI.Education.DigitalESDIntersectionalSourceAcquisitionParetoRound11Exact where

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
-- ROUND 11: SELECTION-BY-TRACE / ELIGIBLE NONRESPONSE / RURAL ACCESS.
--
-- After rounds 9--10, the Python absence-matrix audit identified
-- whoWasExcludedByDesign and whoWasEligibleButMissing as the sparsest fibres.
-- This round therefore targets sources that make exclusion mechanisms literal:
--   * activity thresholds exclude minimally engaged/dropout learners;
--   * an electronically recruited disadvantaged cohort retains identifiable
--     nonresponse/access uncertainty;
--   * rural learners describe low-bandwidth mobile workarounds around scarce
--     infrastructure.
--
-- None of these sources turns missingness into a known causal mechanism without
-- source-specific evidence. Candidate acquisition != final corpus inclusion.
------------------------------------------------------------------------

data Round11Residual : Set where
  activeTraceSelectionExcludesDisengagedLearners : Round11Residual
  eligibleNonresponseMayTrackDigitalAccess : Round11Residual
  ruralLowBandwidthParticipationConstraint : Round11Residual

record Round11Candidate : Set where
  constructor round11-candidate
  field
    source : Attr.AttributedSource
    sourceRoleReceipt : Snowball.SourceRoleSnowballReceipt source
    qidDemand : Identity.ExternalIdentityDemand
    targetResidual : Round11Residual
    auditLens : PhilosophyAudit.PhilosophyAuditFamily
    sourceBoundedReading : String
    limitation : String
    includedInFinalCorpus : Bool
    includedInFinalCorpusIsFalse : includedInFinalCorpus ≡ false

open Round11Candidate public

mkRound11Candidate :
  (source : Attr.AttributedSource) →
  Round11Residual →
  PhilosophyAudit.PhilosophyAuditFamily →
  String →
  String →
  Round11Candidate
mkRound11Candidate source residual lens reading limitation =
  round11-candidate
    source
    (Snowball.canonicalSourceRoleSnowballReceipt source)
    (Identity.mkOptionalIdentityDemand
      "DigitalESDIntersectionalSourceAcquisitionParetoRound11Exact"
      (Attr.sourceTitle source)
      (Attr.sourceTitle source)
      Identity.wikidataQid
      (Identity.unresolved "no independently verified same-object article QID recorded by round 11"))
    residual lens reading limitation false refl

------------------------------------------------------------------------
-- Explicit study-design exclusion of minimally engaged/dropout learners.
------------------------------------------------------------------------

ruanEnglishLearningAnalyticsSource : Attr.AttributedSource
ruanEnglishLearningAnalyticsSource = Attr.mkDOISource
  "Yajun Ruan"
  "English online learning behavior pattern mining and adaptive path inference based on learning analytics"
  "Discover Artificial Intelligence 6, article 976"
  "2026"
  "10.1007/s44163-026-02066-6"
  "https://doi.org/10.1007/s44163-026-02066-6"
  Attr.academicArticleSource
  "Learning-analytics study of an English online-learning platform. The analysis required minimum activity thresholds including login days, total study duration and completed exercises. The paper explicitly acknowledges that this selection systematically excluded minimally engaged learners and dropouts, who may be among those most in need of adaptive support, limiting generalisation to disengaged/irregular learners."
  Attr.publicAttribution

ruanCandidate : Round11Candidate
ruanCandidate = mkRound11Candidate
  ruanEnglishLearningAnalyticsSource
  activeTraceSelectionExcludesDisengagedLearners
  PhilosophyAudit.philosophyClaimProvenancePromotion
  "Near-literal source payment for whoWasExcludedByDesign and whoWasEligibleButMissing: the analytic carrier is constructed by an activity threshold that removes a substantively relevant learner population before behavioural patterns are learned."
  "The source identifies the exclusion and generalisability limit, but does not observe the excluded learners' experiences or prove how their inclusion would change the learned clusters/recommendations."

------------------------------------------------------------------------
-- Eligible disadvantaged cohort, electronic recruitment and nonresponse risk.
------------------------------------------------------------------------

nkosiKeevySource : Attr.AttributedSource
nkosiKeevySource = Attr.mkDOISource
  "Nonhlanhla Precious Nkosi; Monique Keevy"
  "Bridging the digital divide: online learning experiences of disadvantaged students in South Africa"
  "Frontiers in Education 11"
  "2026"
  "10.3389/feduc.2026.1820563"
  "https://doi.org/10.3389/feduc.2026.1820563"
  Attr.academicArticleSource
  "Original qualitative study of disadvantaged accounting students in a South African transformation-focused support programme. An electronic questionnaire was sent to all 231 eligible programme students; 139 completed it (60%). The authors explicitly state that nonrespondents may differ systematically in online engagement or access to digital resources. Follow-up online focus groups also depended on reliable internet access. Respondents reported device, infrastructure, financial and contextual constraints; most respondents were non-first-language English speakers and over half were first-generation university entrants."
  Attr.publicAttribution

nkosiKeevyCandidate : Round11Candidate
nkosiKeevyCandidate = mkRound11Candidate
  nkosiKeevySource
  eligibleNonresponseMayTrackDigitalAccess
  PhilosophyAudit.antiPanopticonVisibilityAuthority
  "Exceptionally useful same-study absence audit: the eligible carrier (231) and realised carrier (139) are both explicit, the recruitment surface is digital, and the authors preserve the possibility that the missing 40% differs precisely on engagement/access coordinates central to the study."
  "The paper states a nonresponse-bias possibility, not an observed causal explanation for each nonresponse. Respondents' lived digital-divide evidence cannot be copied onto absent students, and one disadvantaged accounting programme does not represent all South African students."

------------------------------------------------------------------------
-- Rural learners: practical low-bandwidth route around infrastructure scarcity.
------------------------------------------------------------------------

zwaneMudauSource : Attr.AttributedSource
zwaneMudauSource = Attr.mkDOISource
  "Siyabonga Alpha Zwane; Patience Kelebogile Mudau"
  "South African Rural University Students' Experiences of Open Distance E-Learning Support"
  "International Journal of Learning, Teaching and Educational Research 23(2)"
  "2024"
  "10.26803/ijlter.23.2.3"
  "https://doi.org/10.26803/ijlter.23.2.3"
  Attr.academicArticleSource
  "Qualitative case study based on individual interviews with 15 rural University of South Africa students. Participants described resource/infrastructure scarcity and preferred mobile phones because they could connect with lower bandwidth than computers; mobile/social channels also supported access to learning materials, classes and community."
  Attr.publicAttribution

zwaneMudauCandidate : Round11Candidate
zwaneMudauCandidate = mkRound11Candidate
  zwaneMudauSource
  ruralLowBandwidthParticipationConstraint
  PhilosophyAudit.philosophyClaimProvenancePromotion
  "Direct rural student observer showing that the practical participation carrier can depend on low-bandwidth mobile affordances rather than the nominal availability of an online course. This discriminates formal openness from realised access."
  "Fifteen rural participants and qualitative self-report; successful mobile workaround does not establish infrastructure adequacy, equal learning outcomes, universal rural preference or absence of students who remained entirely disconnected."

canonicalRound11Frontier : List Round11Candidate
canonicalRound11Frontier =
  ruanCandidate
  ∷ nkosiKeevyCandidate
  ∷ zwaneMudauCandidate
  ∷ []

------------------------------------------------------------------------
-- No-promotion / missingness firewalls.
------------------------------------------------------------------------

data Round11CandidateCreatesIncludedStudy : Set where
data ActiveLearnerSelectionCreatesTargetPopulationAdequacy : Set where
data NonresponsePossibilityCreatesObservedAccessCause : Set where
data MobileWorkaroundCreatesInfrastructureAdequacy : Set where

round11CandidateDoesNotCreateIncludedStudy : Round11CandidateCreatesIncludedStudy → ⊥
round11CandidateDoesNotCreateIncludedStudy ()

activeLearnerSelectionDoesNotCreateTargetPopulationAdequacy :
  ActiveLearnerSelectionCreatesTargetPopulationAdequacy → ⊥
activeLearnerSelectionDoesNotCreateTargetPopulationAdequacy ()

nonresponseDoesNotCreateObservedAccessCause :
  NonresponsePossibilityCreatesObservedAccessCause → ⊥
nonresponseDoesNotCreateObservedAccessCause ()

mobileWorkaroundDoesNotCreateInfrastructureAdequacy :
  MobileWorkaroundCreatesInfrastructureAdequacy → ⊥
mobileWorkaroundDoesNotCreateInfrastructureAdequacy ()
