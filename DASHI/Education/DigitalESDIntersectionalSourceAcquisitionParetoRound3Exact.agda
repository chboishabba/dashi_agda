module DASHI.Education.DigitalESDIntersectionalSourceAcquisitionParetoRound3Exact where

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
-- ROUND 3: PUBLIC PROVISION, SOCIAL SUPPORT AND COMMUNITY-RELATIONAL DESIGN.
--
-- This round follows residuals exposed after the first two acquisition fronts:
--   * disability/access x funding/public provision;
--   * remote delivery x disability x social-support continuity;
--   * school-site loss x counselling/pastoral-care continuity;
--   * digital literacy x local culture/community relationship/participation.
--
-- All records remain candidate acquisitions. They do not bypass the declared
-- review search, screening, claim-ceiling, observer, intersection and admission
-- gates.
------------------------------------------------------------------------

data Round3Residual : Set where
  disabilityByFundingFlexibility : Round3Residual
  disabilityBySchoolSocialSupport : Round3Residual
  schoolCounsellingContinuity : Round3Residual
  communityRelationalDigitalLiteracy : Round3Residual

record Round3Candidate : Set where
  constructor round3-candidate
  field
    source : Attr.AttributedSource
    sourceRoleReceipt : Snowball.SourceRoleSnowballReceipt source
    qidDemand : Identity.ExternalIdentityDemand
    pmidPmcidState : String
    deweyState : String
    targetResiduals : List Round3Residual
    observerReading : String
    sourceBoundedReading : String
    limitation : String
    includedInFinalCorpus : Bool
    includedInFinalCorpusIsFalse : includedInFinalCorpus ≡ false

open Round3Candidate public

mkRound3Candidate :
  (source : Attr.AttributedSource) →
  String →
  List Round3Residual →
  String →
  String →
  String →
  Round3Candidate
mkRound3Candidate source pmids residuals observer reading limitation =
  round3-candidate
    source
    (Snowball.canonicalSourceRoleSnowballReceipt source)
    (Identity.mkOptionalIdentityDemand
      "DigitalESDIntersectionalSourceAcquisitionParetoRound3Exact"
      (Attr.sourceTitle source)
      (Attr.sourceTitle source)
      Identity.wikidataQid
      (Identity.unresolved "no independently verified same-object article QID recorded by round 3"))
    pmids
    "Dewey classification unresolved; no nearest-label substitution"
    residuals
    observer
    reading
    limitation
    false refl

------------------------------------------------------------------------
-- Disability x public/individual funding flexibility.
------------------------------------------------------------------------

yatesDickinsonSmithTaniSource : Attr.AttributedSource
yatesDickinsonSmithTaniSource = Attr.mkDOISource
  "Sophie Yates; Helen Dickinson; Catherine Smith; Massimiliano Tani"
  "Flexibility in individual funding schemes: How well did Australia's National Disability Insurance Scheme support remote learning for students with disability during COVID-19?"
  "Social Policy & Administration 55(5), 906-920"
  "2021"
  "10.1111/spol.12670"
  "https://doi.org/10.1111/spol.12670"
  Attr.academicArticleSource
  "Survey of more than 700 families examining how NDIS individual funding supported remote learning for children and young people with disability during the first COVID-19 lockdown; source reports wide variation and service gaps, with useful flexibility depending on information, shared messages, proactive support and system navigation."
  Attr.publicAttribution

yatesCandidate : Round3Candidate
yatesCandidate = mkRound3Candidate
  yatesDickinsonSmithTaniSource
  "PMID 33362318; PMCID PMC7753504 verified"
  (disabilityByFundingFlexibility ∷ [])
  "Family/participant-system observer surface over disability funding and remote-learning support; family survey is not silently treated as direct student testimony."
  "Direct candidate for disability/accessibility x public/individual funding flexibility and service-navigation burden."
  "Pandemic/NDIS Australian context; individualised funding does not by itself establish educational effectiveness, participant authority or universal flexibility."

------------------------------------------------------------------------
-- Disability x school social-support continuity.
------------------------------------------------------------------------

smithTaniYatesDickinsonSource : Attr.AttributedSource
smithTaniYatesDickinsonSource = Attr.mkDOISource
  "Catherine Smith; Massimiliano Tani; Sophie Yates; Helen Dickinson"
  "Successful School Interventions for Students with Disability During Covid-19: Empirical Evidence from Australia"
  "The Asia-Pacific Education Researcher 32, 367-377"
  "2023"
  "10.1007/s40299-022-00659-0"
  "https://doi.org/10.1007/s40299-022-00659-0"
  Attr.academicArticleSource
  "Analysis of an online survey organised by Children and Young People with Disability Australia with responses from more than 700 families; reports gaps in school support and that, when offered, social supports had the strongest positive association with feelings of learner engagement among the examined interventions."
  Attr.publicAttribution

smithCandidate : Round3Candidate
smithCandidate = mkRound3Candidate
  smithTaniYatesDickinsonSource
  "PMCID PMC8994099 verified; PMID not recorded by this atlas"
  (disabilityBySchoolSocialSupport ∷ [])
  "Family-reported school-intervention observer; useful for provisioning/support continuity but not identical to disabled learner self-report."
  "Direct candidate for disability x social-support continuity x remote delivery, preserving the school-intervention and family-report design."
  "Pandemic Australian survey; association of reported social supports with engagement does not create a universal intervention effect or identify all relevant support mechanisms."

------------------------------------------------------------------------
-- School counselling/pastoral care continuity under remote substitution.
------------------------------------------------------------------------

oconnorCounsellingSource : Attr.AttributedSource
oconnorCounsellingSource = Attr.mkDOISource
  "Matt O'Connor"
  "School counselling during COVID-19: an initial examination of school counselling use during a 5-week remote learning period"
  "Pastoral Care in Education 40(1), 81-91"
  "2022"
  "10.1080/02643944.2020.1855674"
  "https://doi.org/10.1080/02643944.2020.1855674"
  Attr.academicArticleSource
  "Australian Prep-to-Grade-12 school study comparing counselling utilisation during a five-week remote-learning period with the same timeframe in the two preceding years; reports fewer students using counselling in 2020 alongside changes in session frequency/focus."
  Attr.publicAttribution

oconnorCandidate : Round3Candidate
oconnorCandidate = mkRound3Candidate
  oconnorCounsellingSource
  "PMID/PMCID not recorded/applicable in this acquisition pass"
  (schoolCounsellingContinuity ∷ [])
  "Institutional service-utilisation observer, not direct evidence of unmet counselling need or participant experience."
  "Direct source candidate for the social-provisioning question: same instructional delivery mode change can alter access/use of school-based pastoral/counselling services."
  "Single Australian school and five-week pandemic period; lower recorded utilisation does not itself prove lower need or causal harm from remote learning."

------------------------------------------------------------------------
-- Community-relational / culturally responsive digital-literacy design.
------------------------------------------------------------------------

rileyMestonWallisKimSource : Attr.AttributedSource
rileyMestonWallisKimSource = Attr.mkDOISource
  "Tasha Riley; Troy Meston; Lynley Wallis; Eun-Ji Amy Kim"
  "From sandstone to screen: a culturally responsive arts-based approach to digital literacy in a remote Indigenous community in Australia"
  "Learning, Media and Technology"
  "2025"
  "10.1080/17439884.2025.2457669"
  "https://doi.org/10.1080/17439884.2025.2457669"
  Attr.academicArticleSource
  "Case study in a remote Queensland Cape York/Quinkan Country primary-school context. The reported project partnered Indigenous and non-Indigenous researchers with the school and describes collaboration with Indigenous Elders, Rangers and learners; data collection included semi-structured yarning interviews, action research, researcher observation/reflection and document analysis."
  Attr.publicAttribution

rileyCandidate : Round3Candidate
rileyCandidate = mkRound3Candidate
  rileyMestonWallisKimSource
  "PMID/PMCID not recorded/applicable in this acquisition pass"
  (communityRelationalDigitalLiteracy ∷ [])
  "Plural community/school/researcher/learner relationship surface. Elders, Rangers and learners are retained in the exact roles the source reports rather than collapsed into a generic Indigenous-authority token."
  "High-alpha candidate for examining how local culture, place, relationships and community participation enter digital-literacy design and evaluation."
  "One situated case. Partnership, yarning and collaboration do not by themselves establish that every participant held equal decision authority, consent authority or benefit-control; those stronger authority claims remain separately auditable."

canonicalRound3Frontier : List Round3Candidate
canonicalRound3Frontier =
  yatesCandidate
  ∷ smithCandidate
  ∷ oconnorCandidate
  ∷ rileyCandidate
  ∷ []

------------------------------------------------------------------------
-- Attribution / observer firewalls.
------------------------------------------------------------------------

data Round3CandidateCreatesIncludedStudy : Set where
data CommunityPartnershipCreatesUniversalIndigenousAuthority : Set where
data FamilySurveyCreatesStudentVoice : Set where
data FundingAvailabilityCreatesEffectiveAccess : Set where
data CounsellingUtilisationCreatesNeedMeasurement : Set where

data SameProgrammeFamilyCreatesSameMeasurementObject : Set where

round3CandidateDoesNotCreateIncludedStudy : Round3CandidateCreatesIncludedStudy → ⊥
round3CandidateDoesNotCreateIncludedStudy ()

communityPartnershipDoesNotCreateUniversalIndigenousAuthority :
  CommunityPartnershipCreatesUniversalIndigenousAuthority → ⊥
communityPartnershipDoesNotCreateUniversalIndigenousAuthority ()

familySurveyDoesNotCreateStudentVoice : FamilySurveyCreatesStudentVoice → ⊥
familySurveyDoesNotCreateStudentVoice ()

fundingAvailabilityDoesNotCreateEffectiveAccess :
  FundingAvailabilityCreatesEffectiveAccess → ⊥
fundingAvailabilityDoesNotCreateEffectiveAccess ()

counsellingUtilisationDoesNotCreateNeedMeasurement :
  CounsellingUtilisationCreatesNeedMeasurement → ⊥
counsellingUtilisationDoesNotCreateNeedMeasurement ()

sameProgrammeFamilyDoesNotCreateSameMeasurementObject :
  SameProgrammeFamilyCreatesSameMeasurementObject → ⊥
sameProgrammeFamilyDoesNotCreateSameMeasurementObject ()
