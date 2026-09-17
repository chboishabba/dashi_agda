module DASHI.Education.DigitalESDIntersectionalSourceAcquisitionParetoExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity

------------------------------------------------------------------------
-- INTERSECTIONAL / WHO-IS-NOT-AT-THE-TABLE SOURCE-ACQUISITION PARETO
--
-- These are candidate acquisition sources selected because they illuminate
-- several currently independent Digital-ESD audit fibres at once. They are not
-- silently promoted into the final included corpus. Search execution,
-- deduplication, eligibility screening, structured extraction and
-- SourceAuditAdmission remain separate downstream gates.
--
-- Source propositions remain source-owned. The residual vocabulary, Pareto
-- ordering and cross-source comparison below are DASHI acquisition synthesis.
------------------------------------------------------------------------

data AcquisitionResidual : Set where
  disabledStudentSituatedVoice : AcquisitionResidual
  disabilityRaceGenderClassInteraction : AcquisitionResidual
  affordabilityHousingLanguageInfrastructure : AcquisitionResidual
  assistiveTechnologySupportContinuity : AcquisitionResidual
  participantCoDesignDecisionAuthority : AcquisitionResidual
  visualImpairmentScreenReaderUsability : AcquisitionResidual
  peerConnectionInstitutionalSupport : AcquisitionResidual
  stakeholderUnderrepresentation : AcquisitionResidual
  privateIncentiveInfrastructureTension : AcquisitionResidual
  realWorldDeploymentGap : AcquisitionResidual
  schoolMealProvisioningContinuity : AcquisitionResidual
  familyTimeCostBurden : AcquisitionResidual

data AcquisitionPriority : Set where
  p0IntersectionalFrontier : AcquisitionPriority
  p1ContextExpansion : AcquisitionPriority
  p2MetadataOnly : AcquisitionPriority

record CandidateIdentityEnvelope (source : Attr.AttributedSource) : Set where
  constructor candidate-identity-envelope
  field
    sourceRoleReceipt : Snowball.SourceRoleSnowballReceipt source
    qidDemand : Identity.ExternalIdentityDemand
    pmidState : String
    deweyState : String
    identifierReading : String

open CandidateIdentityEnvelope public

mkCandidateIdentityEnvelope :
  (source : Attr.AttributedSource) →
  String →
  String →
  String →
  CandidateIdentityEnvelope source
mkCandidateIdentityEnvelope source pmid dewey reading =
  candidate-identity-envelope
    (Snowball.canonicalSourceRoleSnowballReceipt source)
    (Identity.mkOptionalIdentityDemand
      "DigitalESDIntersectionalSourceAcquisitionParetoExact"
      (Attr.sourceTitle source)
      (Attr.sourceTitle source)
      Identity.wikidataQid
      (Identity.unresolved "no independently verified same-object article QID recorded by this acquisition pass"))
    pmid
    dewey
    reading

record AcquisitionCandidate : Set where
  constructor acquisition-candidate
  field
    source : Attr.AttributedSource
    identity : CandidateIdentityEnvelope source
    priority : AcquisitionPriority
    targetResiduals : List AcquisitionResidual
    sourceBoundedReading : String
    limitation : String
    includedInFinalCorpus : Bool
    includedInFinalCorpusIsFalse : includedInFinalCorpus ≡ false

open AcquisitionCandidate public

------------------------------------------------------------------------
-- P0 candidate 1: disabled students, intersectional critical disability,
-- student-centred situated experience.
------------------------------------------------------------------------

krazinskiFoleySource : Attr.AttributedSource
krazinskiFoleySource = Attr.mkDOISource
  "Meaghan Krazinski; Alan Foley"
  "Intersections of Marginalization and Possibility: A Phenomenological Analysis of Disabled Students' Experiences with Online Learning"
  "Journal of Disability Studies in Education 4(1), 98-126"
  "2024"
  "10.1163/25888803-bja10026"
  "https://doi.org/10.1163/25888803-bja10026"
  Attr.academicArticleSource
  "Qualitative phenomenological study centred on disabled students' online-learning experiences using Intersectional Critical Disability Studies and queer phenomenology; supports source-bounded observations about barriers, support, ableism and situated intersections, not prevalence or universal online-learning effects."
  Attr.publicAttribution

krazinskiFoleyCandidate : AcquisitionCandidate
krazinskiFoleyCandidate = acquisition-candidate
  krazinskiFoleySource
  (mkCandidateIdentityEnvelope
    krazinskiFoleySource
    "PMID not recorded/applicable in this acquisition pass"
    "Dewey classification unresolved; no nearest-label substitution"
    "DOI verified; article-level QID unresolved. DOI/QID/Dewey are provenance/index coordinates only.")
  p0IntersectionalFrontier
  ( disabledStudentSituatedVoice
  ∷ disabilityRaceGenderClassInteraction
  ∷ participantCoDesignDecisionAuthority
  ∷ [] )
  "Directly targets the audit's disabled-student observer and intersectional 'who is not at the table?' residual rather than treating disability as a generic equity label."
  "Small qualitative sample and situated US context; student experience does not establish population prevalence or causal intervention effect."
  false refl

------------------------------------------------------------------------
-- P0 candidate 2: Australian multi-level digital inclusion ecology.
------------------------------------------------------------------------

marsdenEtAlSource : Attr.AttributedSource
marsdenEtAlSource = Attr.mkDOISource
  "Linda Marsden; Luke Munn; Liam Magee; Matthew Ferrinda; Justin St. Pierre; Amanda Third"
  "Inclusive online learning in Australia: Barriers and enablers"
  "Education and Information Technologies 30, 5301-5330"
  "2025"
  "10.1007/s10639-024-13012-3"
  "https://doi.org/10.1007/s10639-024-13012-3"
  Attr.academicArticleSource
  "Australian three-school mixed qualitative/workshop/survey study identifying individual, interpersonal, organisational and infrastructural barriers including language, credit rating, housing security, affordability, connectivity and family/teacher digital literacy."
  Attr.publicAttribution

marsdenEtAlCandidate : AcquisitionCandidate
marsdenEtAlCandidate = acquisition-candidate
  marsdenEtAlSource
  (mkCandidateIdentityEnvelope
    marsdenEtAlSource
    "PMID not recorded/applicable in this acquisition pass"
    "Dewey classification unresolved; no nearest-label substitution"
    "DOI verified; article-level QID unresolved. Australian context retained explicitly.")
  p0IntersectionalFrontier
  ( affordabilityHousingLanguageInfrastructure
  ∷ disabledStudentSituatedVoice
  ∷ peerConnectionInstitutionalSupport
  ∷ [] )
  "High-alpha source for the interaction between household material conditions, language, infrastructural provisioning, family/school capability and online-learning inclusion."
  "Three Western Australian schools; does not establish national prevalence or a universal intervention effect."
  false refl

------------------------------------------------------------------------
-- P0 candidate 3: disabled students, AT, co-design and support continuity.
------------------------------------------------------------------------

mcnichollEtAlSource : Attr.AttributedSource
mcnichollEtAlSource = Attr.mkDOISource
  "Aoife McNicholl; Deirdre Desmond; Pamela Gallagher"
  "Learnings from assistive technology use in an online, higher education environment"
  "Disability and Rehabilitation: Assistive Technology 21(5), 1983-1995"
  "2026"
  "10.1080/17483107.2026.2623463"
  "https://doi.org/10.1080/17483107.2026.2623463"
  Attr.academicArticleSource
  "Semi-structured interviews with 13 disabled higher-education students in Ireland on assistive-technology use, inclusive support systems, collaborative spaces, systemic attitudes and co-design of supports."
  Attr.publicAttribution

mcnichollEtAlCandidate : AcquisitionCandidate
mcnichollEtAlCandidate = acquisition-candidate
  mcnichollEtAlSource
  (mkCandidateIdentityEnvelope
    mcnichollEtAlSource
    "PMID 41631993 verified"
    "Dewey classification unresolved; no nearest-label substitution"
    "DOI and PMID verified independently; article-level QID unresolved.")
  p0IntersectionalFrontier
  ( assistiveTechnologySupportContinuity
  ∷ participantCoDesignDecisionAuthority
  ∷ disabledStudentSituatedVoice
  ∷ [] )
  "Direct participant evidence for the audit intersection disability/access x support continuity x co-design/decision voice."
  "Qualitative n=13 Ireland higher-education context; does not establish prevalence or effectiveness of a named assistive technology."
  false refl

------------------------------------------------------------------------
-- P0 candidate 4: visual impairment, screen readers, usability and support.
------------------------------------------------------------------------

rajapaksheEtAlSource : Attr.AttributedSource
rajapaksheEtAlSource = Attr.mkDOISource
  "Wasantha Rajapakshe; Colinie Wickramaarachchi; M.K. Siyumi S. Alwis; A.A. Malsha L. Amarasinghe; P.N. Jayasekara; P.T. Jayasekara"
  "Accessibility and usability of virtual learning platforms: Lived experiences of visually impaired undergraduates in Sri Lanka"
  "Social Sciences & Humanities Open 13, 102621"
  "2026"
  "10.1016/j.ssaho.2026.102621"
  "https://doi.org/10.1016/j.ssaho.2026.102621"
  Attr.academicArticleSource
  "Semi-structured interviews with 15 visually impaired undergraduates in Sri Lanka reporting platform-design, screen-reader, institutional-support, peer-interaction and academic-support experiences."
  Attr.publicAttribution

rajapaksheEtAlCandidate : AcquisitionCandidate
rajapaksheEtAlCandidate = acquisition-candidate
  rajapaksheEtAlSource
  (mkCandidateIdentityEnvelope
    rajapaksheEtAlSource
    "PMID not recorded/applicable in this acquisition pass"
    "Dewey classification unresolved; no nearest-label substitution"
    "DOI and author list verified against publisher/institutional repository; article-level QID unresolved.")
  p0IntersectionalFrontier
  ( visualImpairmentScreenReaderUsability
  ∷ peerConnectionInstitutionalSupport
  ∷ disabledStudentSituatedVoice
  ∷ [] )
  "Directly probes the audit collision between formal platform availability/usability and realised accessibility for a situated disabled learner population."
  "Qualitative n=15 Sri Lankan undergraduate context; does not establish universal platform rankings or population prevalence."
  false refl

------------------------------------------------------------------------
-- P0 candidate 5: explicit stakeholder inclusion / incentive audit of EduNLP.
------------------------------------------------------------------------

gaudeauEtAlSource : Attr.AttributedSource
gaudeauEtAlSource = Attr.mkDOISource
  "Gabrielle Gaudeau; Aoife O'Driscoll; Jasper Degraeuwe; Andrew Caines; Donya Rooein; Zeerak Talat"
  "Incentives Of EdTech: A Systematic Review Of EduNLP Research"
  "Proceedings of the 21st Workshop on Innovative Use of NLP for Building Educational Applications (BEA 2026), 715-750"
  "2026"
  "10.18653/v1/2026.bea-1.50"
  "https://doi.org/10.18653/v1/2026.bea-1.50"
  Attr.academicArticleSource
  "Systematic review of 204 recent EduNLP papers examining stakeholder inclusion, research tasks, incentives, deployment and ethical engagement; reports teacher under-representation and a tension between private-sector incentives and educational-infrastructure needs."
  Attr.publicAttribution

gaudeauEtAlCandidate : AcquisitionCandidate
gaudeauEtAlCandidate = acquisition-candidate
  gaudeauEtAlSource
  (mkCandidateIdentityEnvelope
    gaudeauEtAlSource
    "PMID not applicable/recorded"
    "Dewey classification unresolved; no nearest-label substitution"
    "Published ACL/BEA DOI verified; arXiv 2606.13691 exists as a distinct preprint identity; article-level QID unresolved.")
  p0IntersectionalFrontier
  ( stakeholderUnderrepresentation
  ∷ privateIncentiveInfrastructureTension
  ∷ realWorldDeploymentGap
  ∷ [] )
  "Direct methodological precedent for asking whose interests are represented in EdTech research and connecting stakeholder absence to incentive structure and deployment reality."
  "Review is bounded to its EduNLP/ACL corpus; its stakeholder percentages do not generalise automatically to all EdTech or Digital-ESD literature."
  false refl

------------------------------------------------------------------------
-- P0 candidate 6: school closure, meals, reach and family burden.
------------------------------------------------------------------------

kenneyEtAlSource : Attr.AttributedSource
kenneyEtAlSource = Attr.mkDOISource
  "Erica L. Kenney; Lina Pinero Walkinshaw; Ye Shen; Sheila E. Fleischhacker; Jessica Jones-Smith; Sara N. Bleich; James W. Krieger"
  "Costs, Reach, and Benefits of COVID-19 Pandemic Electronic Benefit Transfer and Grab-and-Go School Meals for Ensuring Youths' Access to Food During School Closures"
  "JAMA Network Open 5(8), e2229514"
  "2022"
  "10.1001/jamanetworkopen.2022.29514"
  "https://doi.org/10.1001/jamanetworkopen.2022.29514"
  Attr.academicArticleSource
  "US cross-sectional economic evaluation of two programmes replacing school-meal access during school closures, retaining eligible population, programme reach, benefits, implementation costs and family time costs."
  Attr.publicAttribution

kenneyEtAlCandidate : AcquisitionCandidate
kenneyEtAlCandidate = acquisition-candidate
  kenneyEtAlSource
  (mkCandidateIdentityEnvelope
    kenneyEtAlSource
    "PMID not recorded by this acquisition pass"
    "Dewey classification unresolved; no nearest-label substitution"
    "DOI verified against JAMA; article-level QID unresolved.")
  p0IntersectionalFrontier
  ( schoolMealProvisioningContinuity
  ∷ familyTimeCostBurden
  ∷ affordabilityHousingLanguageInfrastructure
  ∷ [] )
  "Direct payment for the proposition that loss of school-site access can disrupt non-instructional food provisioning and shift implementation/time burdens onto families; useful for social-provisioning continuity rather than online-learning effect."
  "US pandemic school-closure/programme context; does not show that online education itself universally causes food insecurity."
  false refl

------------------------------------------------------------------------
-- Secondary expansion candidates retained below the first frontier.
------------------------------------------------------------------------

maCuiZhouSource : Attr.AttributedSource
maCuiZhouSource = Attr.mkDOISource
  "Liping Ma; Haili Cui; Xuehan Zhou"
  "Examining the digital divide in online learning during the COVID-19 pandemic: Evidence from undergraduates at 28 research universities"
  "Technology in Society 86, 103280"
  "2026"
  "10.1016/j.techsoc.2026.103280"
  "https://doi.org/10.1016/j.techsoc.2026.103280"
  Attr.academicArticleSource
  "Survey of 11,501 undergraduates at 28 Chinese research universities examining family-background disparities and school, family and individual obstacles to perceived online-learning effectiveness."
  Attr.publicAttribution

maCuiZhouCandidate : AcquisitionCandidate
maCuiZhouCandidate = acquisition-candidate
  maCuiZhouSource
  (mkCandidateIdentityEnvelope
    maCuiZhouSource
    "PMID not recorded/applicable in this acquisition pass"
    "Dewey classification unresolved; no nearest-label substitution"
    "DOI verified; article-level QID unresolved.")
  p1ContextExpansion
  ( affordabilityHousingLanguageInfrastructure ∷ [] )
  "Large multi-university socioeconomic/family-context comparator useful after the smaller situated P0 sources."
  "Perceived effectiveness and family-background associations do not by themselves identify causal mechanism or disability-specific interaction."
  false refl

aliPrompiengchaiJoordensSource : Attr.AttributedSource
aliPrompiengchaiJoordensSource = Attr.mkDOISource
  "Hannah Ali; Sapolnach Prompiengchai; Steve Joordens"
  "Educational Technology Procurement at Canadian Colleges and Universities: An Environmental Scan"
  "Standards 4(1), 1-24"
  "2024"
  "10.3390/standards4010001"
  "https://doi.org/10.3390/standards4010001"
  Attr.academicArticleSource
  "Mixed-method environmental scan of EdTech procurement at Canadian post-secondary institutions, including privacy/security, accessibility, care-of-data standards and centralisation challenges."
  Attr.publicAttribution

aliPrompiengchaiJoordensCandidate : AcquisitionCandidate
aliPrompiengchaiJoordensCandidate = acquisition-candidate
  aliPrompiengchaiJoordensSource
  (mkCandidateIdentityEnvelope
    aliPrompiengchaiJoordensSource
    "PMID not applicable/recorded"
    "Dewey classification unresolved; no nearest-label substitution"
    "DOI verified; article-level QID unresolved.")
  p1ContextExpansion
  ( privateIncentiveInfrastructureTension
  ∷ stakeholderUnderrepresentation
  ∷ [] )
  "Useful procurement/standards comparator for who participates in institutional EdTech selection and which accessibility/privacy criteria enter decisions."
  "Questionnaire responses from 10 institutions and two interviews; procurement-manager perspective cannot stand in for student/disabled-participant authority."
  false refl

canonicalP0IntersectionalFrontier : List AcquisitionCandidate
canonicalP0IntersectionalFrontier =
  krazinskiFoleyCandidate
  ∷ marsdenEtAlCandidate
  ∷ mcnichollEtAlCandidate
  ∷ rajapaksheEtAlCandidate
  ∷ gaudeauEtAlCandidate
  ∷ kenneyEtAlCandidate
  ∷ []

canonicalP1ContextExpansion : List AcquisitionCandidate
canonicalP1ContextExpansion =
  maCuiZhouCandidate
  ∷ aliPrompiengchaiJoordensCandidate
  ∷ []

------------------------------------------------------------------------
-- Pareto / attribution firewalls.
------------------------------------------------------------------------

data CandidateSourceCreatesIncludedStudy : Set where
data ParetoPriorityCreatesAuthority : Set where
data IdentifierCompletenessCreatesEvidenceCompleteness : Set where
data HighResidualCoverageCreatesTruth : Set where
data OneSituatedSourceClosesIntersectionalCorpus : Set where

candidateSourceDoesNotCreateIncludedStudy : CandidateSourceCreatesIncludedStudy → ⊥
candidateSourceDoesNotCreateIncludedStudy ()

paretoPriorityDoesNotCreateAuthority : ParetoPriorityCreatesAuthority → ⊥
paretoPriorityDoesNotCreateAuthority ()

identifierCompletenessDoesNotCreateEvidenceCompleteness :
  IdentifierCompletenessCreatesEvidenceCompleteness → ⊥
identifierCompletenessDoesNotCreateEvidenceCompleteness ()

highResidualCoverageDoesNotCreateTruth : HighResidualCoverageCreatesTruth → ⊥
highResidualCoverageDoesNotCreateTruth ()

oneSituatedSourceDoesNotCloseIntersectionalCorpus :
  OneSituatedSourceClosesIntersectionalCorpus → ⊥
oneSituatedSourceDoesNotCloseIntersectionalCorpus ()

paretoReading : String
paretoReading =
  "P0 favours candidate sources that jointly illuminate currently weak observer/intersection/provisioning/incentive fibres while retaining exact source scope. Priority is an acquisition heuristic, not evidence authority. Search execution and SourceAuditAdmission remain mandatory before synthesis."
