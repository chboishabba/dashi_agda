module DASHI.Education.DigitalESDIntersectionalSourceAcquisitionParetoRound12Exact where

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
-- ROUND 12: DISCLOSURE-GATED LEGIBILITY / DIAGNOSIS / SUPPORT IMPLEMENTATION.
--
-- The Round-11 Python absence audit leaves whoHadToDiscloseToBeCounted and
-- whoDefinedTheCategories on the P0 frontier, alongside residual exclusion and
-- eligible-but-missing fibres. This round separates five states that are often
-- silently collapsed:
--
--   self-recognition
--   != formal diagnosis
--   != institutional disclosure
--   != granted accommodation
--   != implemented/effective support.
--
-- Sources remain candidate acquisitions only. Disability/neurodivergence facts,
-- institutional legibility and support authority retain distinct provenance.
------------------------------------------------------------------------

data Round12Residual : Set where
  onlineUniversityDisclosureGate : Round12Residual
  quantifiedNeurotypeDisclosureSupportGap : Round12Residual
  diagnosisLegibilityAccommodationImplementationGap : Round12Residual

record Round12Candidate : Set where
  constructor round12-candidate
  field
    source : Attr.AttributedSource
    sourceRoleReceipt : Snowball.SourceRoleSnowballReceipt source
    qidDemand : Identity.ExternalIdentityDemand
    externalIdentifierState : String
    targetResidual : Round12Residual
    auditLens : PhilosophyAudit.PhilosophyAuditFamily
    sourceBoundedReading : String
    limitation : String
    includedInFinalCorpus : Bool
    includedInFinalCorpusIsFalse : includedInFinalCorpus ≡ false

open Round12Candidate public

mkRound12Candidate :
  (source : Attr.AttributedSource) →
  String →
  Round12Residual →
  PhilosophyAudit.PhilosophyAuditFamily →
  String →
  String →
  Round12Candidate
mkRound12Candidate source ids residual lens reading limitation =
  round12-candidate
    source
    (Snowball.canonicalSourceRoleSnowballReceipt source)
    (Identity.mkOptionalIdentityDemand
      "DigitalESDIntersectionalSourceAcquisitionParetoRound12Exact"
      (Attr.sourceTitle source)
      (Attr.sourceTitle source)
      Identity.wikidataQid
      (Identity.unresolved "no independently verified same-object article QID recorded by round 12"))
    ids residual lens reading limitation false refl

------------------------------------------------------------------------
-- Online university: accommodations are disclosure-gated, but disclosure itself
-- has emotional and administrative costs and differs for apparent/hidden needs.
------------------------------------------------------------------------

melianMenesesSource : Attr.AttributedSource
melianMenesesSource = Attr.mkDOISource
  "Efrem Melián; Julio Meneses"
  "Getting ahead in the online university: Disclosure experiences of students with apparent and hidden disabilities"
  "International Journal of Educational Research 114, 101991"
  "2022"
  "10.1016/j.ijer.2022.101991"
  "https://doi.org/10.1016/j.ijer.2022.101991"
  Attr.academicArticleSource
  "Open-access qualitative study using email interviews with 34 disabled students at a Spanish open university. Students had to communicate disability to the university to access accommodations, yet disclosure involved emotional risk and administrative barriers. Apparent physical/sensory and hidden mental-health/learning disabilities showed different disclosure and identity-management strategies."
  Attr.publicAttribution

melianMenesesCandidate : Round12Candidate
melianMenesesCandidate = mkRound12Candidate
  melianMenesesSource
  "DOI verified; article-level QID unresolved"
  onlineUniversityDisclosureGate
  PhilosophyAudit.antiPanopticonVisibilityAuthority
  "Direct Digital-ESD disclosure-gate witness: the online institution cannot infer support need from mere enrolment/participation, while access to accommodation depends on a potentially costly act of becoming institutionally visible. Apparent and hidden disability remain distinct observer/legibility contexts."
  "Thirty-four self-selected students at one Spanish open university. Disclosure barriers do not establish universal non-disclosure rates, one hidden-disability experience, or that disclosure necessarily produces effective accommodation."

------------------------------------------------------------------------
-- AU/NZ quantified disclosure/support differences across neurodivergent and MHC
-- groups, including multiple-minority-identity measurement.
------------------------------------------------------------------------

kennedyRichdaleLawsonSource : Attr.AttributedSource
kennedyRichdaleLawsonSource = Attr.mkDOISource
  "Lyndel J. Kennedy; Amanda L. Richdale; Lauren P. Lawson"
  "Comparing Disclosure and Supports used by Higher-Education Students with Neurodivergent or Mental Health Conditions"
  "Autism in Adulthood 7(4), 462-478"
  "2025"
  "10.1089/aut.2024.0118"
  "https://doi.org/10.1089/aut.2024.0118"
  Attr.academicArticleSource
  "Anonymous online survey of 131 neurodivergent and 42 non-neurodivergent students with mental-health conditions in Australian/New Zealand higher education. Disclosure and support use differed across Autistic, ADHD, AuDHD, ND-other and non-neurodivergent-MHC groups. AuDHD disclosure was 83% versus 19% for NND-MHC; support helpfulness was high among users. Apart from AuDHD, fewer than half of eligible students disclosed or used supports. Minority-identity scores were measured but were not associated with disclosure in this sample."
  Attr.publicAttribution

kennedyCandidate : Round12Candidate
kennedyCandidate = mkRound12Candidate
  kennedyRichdaleLawsonSource
  "DOI 10.1089/aut.2024.0118; PMID 40933678; PMCID PMC12417809 verified"
  quantifiedNeurotypeDisclosureSupportGap
  PhilosophyAudit.philosophyClaimProvenancePromotion
  "Quantified same-study separation of eligibility, disclosure, support use and perceived helpfulness across multiple neurotype/MHC groups. It is especially valuable for the eligible-but-missing and disclose-to-be-counted fibres because institutional visibility and actual support use differ substantially even where students are in the eligible population."
  "Anonymous survey and self-reported diagnostic/disclosure data; group differences do not supply an intersectional causal mechanism. A multiple-minority-identity score does not turn marginal categories into a complete intersectional model."

------------------------------------------------------------------------
-- Australian health-professions graduates: self-recognition, diagnostic
-- legibility, formal accommodation and implementation remain distinct stages.
------------------------------------------------------------------------

grayEtAlSource : Attr.AttributedSource
grayEtAlSource = Attr.mkDOISource
  "Laura Gray; Bryony McNeill; James Woodman; Sarah Bernard; Julie Kos; Yvonne Hewitt; Sophie Goldingay; Alexa Hayley; Danielle Hitch; Susie Macfarlane; Laura Pecora; Valerie Watchorn; Sherryn Evans"
  "You Have So Much to Offer as a Health Professional: Neurodivergent Students' Experiences of Recognition, Disclosure, and Accommodation in Australian Health Professions Education"
  "Teaching and Learning in Medicine"
  "2026"
  "10.1080/10401334.2026.2632753"
  "https://doi.org/10.1080/10401334.2026.2632753"
  Attr.academicArticleSource
  "Open-access Australian survey/thematic study of 183 neurodivergent health-professions graduates, many identifying with multiple forms of neurodivergence. The study distinguishes self-recognition from institutional recognition, describes educational accommodation systems often predicated on formal diagnosis/disclosure, reports barriers to diagnosis and disclosure, and finds that formally granted accommodations were sometimes inconsistently implemented."
  Attr.publicAttribution

grayCandidate : Round12Candidate
grayCandidate = mkRound12Candidate
  grayEtAlSource
  "DOI 10.1080/10401334.2026.2632753; PMID 41718571 verified; article-level QID unresolved"
  diagnosisLegibilityAccommodationImplementationGap
  PhilosophyAudit.philosophyClaimProvenancePromotion
  "Highest-dimensional Round-12 source: the same person can move through self-recognition, diagnosis, institutional disclosure, formal grant and implementation as non-equivalent states. This directly attacks category-definition and disclosure-gated legibility without treating institutional recognition as the underlying person's truth."
  "Graduate retrospective sample across Australian health-professions programmes; qualitative/thematic evidence does not estimate population prevalence or causal effects of a particular accommodation. Formal diagnosis and self-recognition remain distinct evidence carriers rather than competing truth tokens."

canonicalRound12Frontier : List Round12Candidate
canonicalRound12Frontier =
  grayCandidate
  ∷ melianMenesesCandidate
  ∷ kennedyCandidate
  ∷ []

------------------------------------------------------------------------
-- No-promotion / legibility firewalls.
------------------------------------------------------------------------

data Round12CandidateCreatesIncludedStudy : Set where
data NonDisclosureCreatesNoDisabilityOrNeed : Set where
data FormalDiagnosisCreatesRealisedAccommodation : Set where
data GrantedAccommodationCreatesImplementedAccommodation : Set where
data MultipleMinorityIdentityMeasurementCreatesIntersectionalCause : Set where

data SelfRecognitionCreatesFormalDiagnosis : Set where
data InstitutionalDisclosureCreatesEffectiveSupport : Set where

round12CandidateDoesNotCreateIncludedStudy : Round12CandidateCreatesIncludedStudy → ⊥
round12CandidateDoesNotCreateIncludedStudy ()

nonDisclosureDoesNotCreateNoDisabilityOrNeed :
  NonDisclosureCreatesNoDisabilityOrNeed → ⊥
nonDisclosureDoesNotCreateNoDisabilityOrNeed ()

formalDiagnosisDoesNotCreateRealisedAccommodation :
  FormalDiagnosisCreatesRealisedAccommodation → ⊥
formalDiagnosisDoesNotCreateRealisedAccommodation ()

grantedAccommodationDoesNotCreateImplementedAccommodation :
  GrantedAccommodationCreatesImplementedAccommodation → ⊥
grantedAccommodationDoesNotCreateImplementedAccommodation ()

multipleMinorityIdentityMeasurementDoesNotCreateIntersectionalCause :
  MultipleMinorityIdentityMeasurementCreatesIntersectionalCause → ⊥
multipleMinorityIdentityMeasurementDoesNotCreateIntersectionalCause ()

selfRecognitionDoesNotCreateFormalDiagnosis : SelfRecognitionCreatesFormalDiagnosis → ⊥
selfRecognitionDoesNotCreateFormalDiagnosis ()

institutionalDisclosureDoesNotCreateEffectiveSupport :
  InstitutionalDisclosureCreatesEffectiveSupport → ⊥
institutionalDisclosureDoesNotCreateEffectiveSupport ()
