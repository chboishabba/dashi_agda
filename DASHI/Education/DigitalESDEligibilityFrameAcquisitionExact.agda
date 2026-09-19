module DASHI.Education.DigitalESDEligibilityFrameAcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Education.DigitalESDEligibilityFrameExclusionExact as Frame

------------------------------------------------------------------------
-- DIGITAL-ESD ELIGIBILITY-FRAME ACQUISITION FRONTIER
--
-- Python/Pareto selection target:
--   * target population -> sampling-frame contraction;
--   * administrative-frame undercoverage;
--   * category/data omission inside educational infrastructure.
--
-- These sources are candidate acquisition objects only.  They do not thereby
-- enter the final review corpus and they do not populate DASHI's finite frame
-- collision.  QIDs remain unresolved unless a same-object publication item is
-- independently verified.  Dewey remains navigation-only.
------------------------------------------------------------------------

data EligibilityFrameResidual : Set where
  populationToSurveyableFrameContraction : EligibilityFrameResidual
  administrativeFrameSubgroupUndercoverage : EligibilityFrameResidual
  administrativeCategoryPreclusionOmission : EligibilityFrameResidual

record EligibilityFrameCandidate : Set where
  constructor eligibility-frame-candidate
  field
    source : Attr.AttributedSource
    sourceRoleReceipt : Snowball.SourceRoleSnowballReceipt source
    qidDemand : Identity.ExternalIdentityDemand
    deweyState : String
    targetResidual : EligibilityFrameResidual
    sourceBoundedReading : String
    limitation : String
    includedInFinalCorpus : Bool
    includedInFinalCorpusIsFalse : includedInFinalCorpus ≡ false

open EligibilityFrameCandidate public

mkEligibilityFrameCandidate :
  (source : Attr.AttributedSource) →
  EligibilityFrameResidual →
  String →
  String →
  EligibilityFrameCandidate
mkEligibilityFrameCandidate source residual reading limitation =
  eligibility-frame-candidate
    source
    (Snowball.canonicalSourceRoleSnowballReceipt source)
    (Identity.mkOptionalIdentityDemand
      "DigitalESDEligibilityFrameAcquisitionExact"
      (Attr.sourceTitle source)
      (Attr.sourceTitle source)
      Identity.wikidataQid
      (Identity.unresolved
        "no independently verified same-object publication QID recorded for eligibility-frame acquisition"))
    "Dewey classification unresolved; navigation only and no nearest-label substitution"
    residual
    reading
    limitation
    false
    refl

------------------------------------------------------------------------
-- NCVER 2024: population -> sampling frame -> invitation.
------------------------------------------------------------------------

ncver2024StudentOutcomesTechnicalNotes : Attr.AttributedSource
ncver2024StudentOutcomesTechnicalNotes = Attr.mkNoDOISource
  "National Centre for Vocational Education Research"
  "National Student Outcomes Survey 2024 — technical notes"
  "NCVER support document"
  "2024"
  "https://www.ncver.edu.au/__data/assets/pdf_file/0041/9692735/2024_SOS_technical_notes.pdf"
  Attr.institutionalSource
  "Australian institutional methodology source. It separately defines survey scope/population, sampling-frame construction and invitations. The sampling frame is restricted to de-duplicated population records available for surveying and with obtainable contact details, with exclusions applied before sampling."
  Attr.publicAttribution

ncverCandidate : EligibilityFrameCandidate
ncverCandidate = mkEligibilityFrameCandidate
  ncver2024StudentOutcomesTechnicalNotes
  populationToSurveyableFrameContraction
  "Direct upstream-frame donor: the named population, surveyable/contactable sampling frame and invited sample are distinct same-program objects. It therefore pays the question 'who was never carried from the target population into the surveyable frame?' without treating later response as the only missingness mechanism."
  "Institutional technical notes describe the 2024 Australian VET survey design and cannot establish an individual educational effect, a universal contactability mechanism, or that every excluded record corresponds to disadvantage."



------------------------------------------------------------------------
-- QILT / Social Research Centre 2022: higher-education population frame.
------------------------------------------------------------------------

qilt2022SESMethodologicalSource : Attr.AttributedSource
qilt2022SESMethodologicalSource = Attr.mkNoDOISource
  "Social Research Centre"
  "2022 Student Experience Survey Methodological Report"
  "Quality Indicators for Learning and Teaching (QILT)"
  "2022"
  "https://www.qilt.edu.au/docs/default-source/default-document-library/ses-2022-methodological-report---accessible011f286115974581a347d02cafe4bb48.pdf"
  Attr.institutionalSource
  "Australian higher-education survey methodology source. TCSI extracts are reviewed to identify records eligible for the Student Experience Survey; institutions can add enrolments missing from the extract; submitted templates are combined into a population frame and exclusion rules are applied before final institution population files are produced."
  Attr.publicAttribution

qilt2022Candidate : EligibilityFrameCandidate
qilt2022Candidate = mkEligibilityFrameCandidate
  qilt2022SESMethodologicalSource
  populationToSurveyableFrameContraction
  "Independent Australian higher-education frame-construction donor: eligibility identification, missing-enrolment supplementation and exclusion rules are explicit stages between institutional enrolment data and the final survey population frame. A clean final frame therefore cannot by itself recover records omitted before or during construction."
  "Institutional methodology source, not participant-outcome evidence. The report documents the survey's construction process and does not establish that an omitted record represents harm, disadvantage or an incorrect exclusion."

------------------------------------------------------------------------
-- Voorheis 2021: alternate administrative frame coverage for college graduates.
------------------------------------------------------------------------

voorheis2021NSCGFrameSource : Attr.AttributedSource
voorheis2021NSCGFrameSource = Attr.mkNoDOISource
  "John Voorheis"
  "Evaluating Administrative Records as a Potential Sample Frame for the National Survey of College Graduates"
  "U.S. Census Bureau CARRA Working Paper 18-14"
  "2021 publication; written 2018"
  "https://www2.census.gov/ces/wp/2018/CARRA-18-14.pdf"
  (Attr.namedSourceKind "government working paper")
  "Government research working paper comparing National Student Clearinghouse administrative records with the ACS-derived National Survey of College Graduates frame. It reports non-uniform coverage across degree type and demographic/occupational subgroups and treats frame replacement/supplementation as an empirical coverage question."
  Attr.publicAttribution

voorheisCandidate : EligibilityFrameCandidate
voorheisCandidate = mkEligibilityFrameCandidate
  voorheis2021NSCGFrameSource
  administrativeFrameSubgroupUndercoverage
  "Same-object frame-comparison donor: an administrative education-record source can have high aggregate coverage while still under-covering particular subgroups. Aggregate frame coverage therefore cannot silently stand in for subgroup coverage."
  "The analysed National Student Clearinghouse extract is geographically/temporally constrained and the source itself does not establish the full-current-NSC coverage state or a Digital-ESD intervention effect."



------------------------------------------------------------------------
-- Dynarski / Hemelt / Hyman 2015: subgroup-specific administrative coverage.
------------------------------------------------------------------------

dynarskiHemeltHymanSource : Attr.AttributedSource
dynarskiHemeltHymanSource = Attr.mkDOISource
  "Susan M. Dynarski; Steven W. Hemelt; Joshua M. Hyman"
  "The Missing Manual: Using National Student Clearinghouse Data to Track Postsecondary Outcomes"
  "Educational Evaluation and Policy Analysis 37(1_suppl):53S-79S"
  "2015"
  "10.3102/0162373715576078"
  "https://doi.org/10.3102/0162373715576078"
  Attr.academicArticleSource
  "Empirical/methodological study of National Student Clearinghouse coverage. It estimates coverage by state, institution type and demographic subgroup, reports lower coverage for some minority and for-profit-college populations, and discusses suppressed records and matching errors as additional sources of noncoverage."
  Attr.publicAttribution

dynarskiHemeltHymanCandidate : EligibilityFrameCandidate
dynarskiHemeltHymanCandidate = mkEligibilityFrameCandidate
  dynarskiHemeltHymanSource
  administrativeFrameSubgroupUndercoverage
  "Independent subgroup-undercoverage donor: high aggregate administrative coverage can coexist with lower coverage for specific institution and demographic groups, so aggregate frame adequacy cannot recover subgroup frame adequacy."
  "Source-specific NSC coverage analysis; it does not establish the current coverage state of every administrative education system, nor a Digital-ESD intervention effect."



------------------------------------------------------------------------
-- Creagh 2016: category construction can erase within-category difference.
------------------------------------------------------------------------

creaghLBOTESource : Attr.AttributedSource
creaghLBOTESource = Attr.mkDOISource
  "Sue Creagh"
  "A critical analysis of the Language Background Other Than English (LBOTE) category in the Australian national testing system: a Foucauldian perspective"
  "Journal of Education Policy 31(3):275-289"
  "2016"
  "10.1080/02680939.2015.1066870"
  "https://doi.org/10.1080/02680939.2015.1066870"
  Attr.academicArticleSource
  "Australian national-testing analysis of the LBOTE statistical category. The source argues that aggregating heterogeneous students under LBOTE can homogenise variation and obscure the relation between language background and test performance."
  Attr.publicAttribution

creaghLBOTECandidate : EligibilityFrameCandidate
creaghLBOTECandidate = mkEligibilityFrameCandidate
  creaghLBOTESource
  administrativeCategoryPreclusionOmission
  "Independent category-construction donor: inclusion in an administrative/statistical category does not guarantee that the category preserves distinctions needed by a downstream equity or pedagogy consumer."
  "Foucauldian/source-bounded analysis of the Australian LBOTE category; it does not establish one universal category ontology, one causal educational effect, or that every use of an aggregate language category is invalid."

------------------------------------------------------------------------
-- Clutterbuck / Hardy / Creagh 2023 issue, 2021 online: OneSchool omissions.
------------------------------------------------------------------------

clutterbuckHardyCreaghSource : Attr.AttributedSource
clutterbuckHardyCreaghSource = Attr.mkDOISource
  "Jennifer Clutterbuck; Ian Hardy; Sue Creagh"
  "Data infrastructures as sites of preclusion and omission: the representation of students and schooling"
  "Journal of Education Policy 38(1):93-114"
  "2023 issue / 2021 online"
  "10.1080/02680939.2021.1972166"
  "https://doi.org/10.1080/02680939.2021.1972166"
  Attr.academicArticleSource
  "Australian education-data-infrastructure study focused on Queensland OneSchool. The source analyses how infrastructure can authorise preclusion/omission in student representation, including omission of important enrolment information about Indigenous languages."
  Attr.publicAttribution

clutterbuckCandidate : EligibilityFrameCandidate
clutterbuckCandidate = mkEligibilityFrameCandidate
  clutterbuckHardyCreaghSource
  administrativeCategoryPreclusionOmission
  "Category/register-construction donor: who becomes representable can depend on which fields and categories the administrative infrastructure authorises. Presence in the administrative system therefore does not imply that all consumer-relevant student characteristics are represented."
  "The paper supports bounded claims about OneSchool/data infrastructure and representation. It does not establish an individual outcome for every student, universal intentional exclusion, or that omitted information would by itself change a downstream decision."

canonicalEligibilityFrameAcquisitionFrontier : List EligibilityFrameCandidate
canonicalEligibilityFrameAcquisitionFrontier =
  ncverCandidate
  ∷ qilt2022Candidate
  ∷ voorheisCandidate
  ∷ dynarskiHemeltHymanCandidate
  ∷ creaghLBOTECandidate
  ∷ clutterbuckCandidate
  ∷ []

------------------------------------------------------------------------
-- Reuse the theorem-bearing frame owner without transferring source authority.
------------------------------------------------------------------------

eligibilityFrameBoundary : Frame.EligibilityFrameBoundary
eligibilityFrameBoundary = Frame.canonicalEligibilityFrameBoundary

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data EligibilityFrameCandidateCreatesIncludedStudy : Set where
data InstitutionalFrameCreatesPopulationTruth : Set where
data CategoryOmissionCreatesIndividualOutcome : Set where
data AggregateCoverageCreatesSubgroupCoverage : Set where
data AdministrativePresenceCreatesCompleteRepresentation : Set where

eligibilityFrameCandidateDoesNotCreateIncludedStudy :
  EligibilityFrameCandidateCreatesIncludedStudy → ⊥
eligibilityFrameCandidateDoesNotCreateIncludedStudy ()

institutionalFrameDoesNotCreatePopulationTruth :
  InstitutionalFrameCreatesPopulationTruth → ⊥
institutionalFrameDoesNotCreatePopulationTruth ()

categoryOmissionDoesNotCreateIndividualOutcome :
  CategoryOmissionCreatesIndividualOutcome → ⊥
categoryOmissionDoesNotCreateIndividualOutcome ()

aggregateCoverageDoesNotCreateSubgroupCoverage :
  AggregateCoverageCreatesSubgroupCoverage → ⊥
aggregateCoverageDoesNotCreateSubgroupCoverage ()

administrativePresenceDoesNotCreateCompleteRepresentation :
  AdministrativePresenceCreatesCompleteRepresentation → ⊥
administrativePresenceDoesNotCreateCompleteRepresentation ()

eligibilityFrameAcquisitionReading : String
eligibilityFrameAcquisitionReading =
  "The upstream Digital-ESD acquisition frontier now distinguishes surveyable-frame contraction, subgroup undercoverage in an administrative frame, and category/data omission inside educational infrastructure. NCVER, Voorheis, and Clutterbuck/Hardy/Creagh own only their bounded source propositions. DASHI separately owns the finite nonfactorability theorem in DigitalESDEligibilityFrameExclusionExact. Candidate acquisition, identifier completeness, institutional authority, or administrative presence never creates final-corpus inclusion or complete population truth."
