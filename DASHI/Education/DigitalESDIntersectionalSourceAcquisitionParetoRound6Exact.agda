module DASHI.Education.DigitalESDIntersectionalSourceAcquisitionParetoRound6Exact where

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
-- ROUND 6: PRACTICAL EXIT / CONSENT SELECTION / CLASSIFICATION / DATA VALUE.
--
-- The hyperfabric residual is no longer merely whether privacy or inclusion is
-- mentioned. We need evidence about who can refuse, whether refusal is itself
-- patterned, which groups are absent from bias research, and how student data
-- become economically valuable or operationally consequential.
------------------------------------------------------------------------

data Round6Residual : Set where
  consentSelectionByStudentDifference : Round6Residual
  algorithmicClassificationByWhoIsStudied : Round6Residual
  disabilityAnalyticsByEvidenceGap : Round6Residual
  dataMonetisationByUserControlAndPoliticalEconomy : Round6Residual

record Round6Candidate : Set where
  constructor round6-candidate
  field
    source : Attr.AttributedSource
    sourceRoleReceipt : Snowball.SourceRoleSnowballReceipt source
    qidDemand : Identity.ExternalIdentityDemand
    externalIdentityState : String
    deweyState : String
    targetResidual : Round6Residual
    auditLens : PhilosophyAudit.PhilosophyAuditFamily
    sourceBoundedReading : String
    limitation : String
    includedInFinalCorpus : Bool
    includedInFinalCorpusIsFalse : includedInFinalCorpus ≡ false

open Round6Candidate public

mkRound6Candidate :
  (source : Attr.AttributedSource) →
  String →
  Round6Residual →
  PhilosophyAudit.PhilosophyAuditFamily →
  String →
  String →
  Round6Candidate
mkRound6Candidate source identity residual audit reading limitation =
  round6-candidate
    source
    (Snowball.canonicalSourceRoleSnowballReceipt source)
    (Identity.mkOptionalIdentityDemand
      "DigitalESDIntersectionalSourceAcquisitionParetoRound6Exact"
      (Attr.sourceTitle source)
      (Attr.sourceTitle source)
      Identity.wikidataQid
      (Identity.unresolved "no independently verified same-object article QID recorded by round 6"))
    identity
    "Dewey classification unresolved; no nearest-label substitution"
    residual
    audit
    reading
    limitation
    false refl

------------------------------------------------------------------------
-- Who opts in/out is itself an intersectional observation.
------------------------------------------------------------------------

liSunSchaubBrooksSource : Attr.AttributedSource
liSunSchaubBrooksSource = Attr.mkDOISource
  "Warren Li; Kaiwen Sun; Florian Schaub; Christopher Brooks"
  "Disparities in Students' Propensity to Consent to Learning Analytics"
  "International Journal of Artificial Intelligence in Education 32(3), 564-608"
  "2022"
  "10.1007/s40593-021-00254-2"
  "https://doi.org/10.1007/s40593-021-00254-2"
  Attr.academicArticleSource
  "Empirical university-student study of consent propensity, opt-in/opt-out framing, perceived learning-analytics benefits and privacy concerns; explicitly motivates concern that differential opt-out can alter predictive datasets and model bias."
  Attr.publicAttribution

liCandidate : Round6Candidate
liCandidate = mkRound6Candidate
  liSunSchaubBrooksSource
  "DOI verified; QID/PMID/PMCID not independently recorded in this acquisition pass"
  consentSelectionByStudentDifference
  PhilosophyAudit.antiPanopticonVisibilityAuthority
  "High-alpha source for practical-exit x representation: offering a choice does not imply the retained analytics population is representative, because consent propensity may differ across student groups and privacy/benefit perceptions."
  "Consent propensity in one higher-education study does not determine legal validity of consent, actual freedom from educational penalty, downstream model bias in every system, or participant decision authority over institutional analytics."

------------------------------------------------------------------------
-- Which groups are known/unknown in algorithmic-bias evidence.
------------------------------------------------------------------------

bakerHawnBiasSource : Attr.AttributedSource
bakerHawnBiasSource = Attr.mkDOISource
  "Ryan S. Baker; Aaron Hawn"
  "Algorithmic Bias in Education"
  "International Journal of Artificial Intelligence in Education 32(4), 1052-1092"
  "2022"
  "10.1007/s40593-021-00285-9"
  "https://doi.org/10.1007/s40593-021-00285-9"
  Attr.academicArticleSource
  "Review of empirical algorithmic-bias evidence in education, including which groups and pipeline stages are studied. It contrasts heavily studied race/ethnicity, gender and nationality with thinner evidence for socioeconomic status, disability and military-connected status and explicitly frames unknown-bias residuals."
  Attr.publicAttribution

bakerHawnCandidate : Round6Candidate
bakerHawnCandidate = mkRound6Candidate
  bakerHawnBiasSource
  "DOI verified; article QID unresolved"
  algorithmicClassificationByWhoIsStudied
  PhilosophyAudit.philosophyClaimProvenancePromotion
  "Direct acquisition donor for the hyperfabric's 'who is not at the table / who is not measured' question at the algorithmic-classification layer: known fairness evidence and unstudied group intersections remain distinct."
  "Review-level synthesis does not prove bias in a named Digital-ESD system, does not establish equal evidentiary support across groups, and cannot manufacture a causal mechanism or remediation effect."

------------------------------------------------------------------------
-- Disability-focused learning-analytics evidence map.
------------------------------------------------------------------------

khalilSladePrinslooSource : Attr.AttributedSource
khalilSladePrinslooSource = Attr.mkDOISource
  "Mohammad Khalil; Sharon Slade; Paul Prinsloo"
  "Learning analytics in support of inclusiveness and disabled students: a systematic review"
  "Journal of Computing in Higher Education 36, 202-219"
  "2023 online / 2024 issue"
  "10.1007/s12528-023-09363-4"
  "https://doi.org/10.1007/s12528-023-09363-4"
  Attr.academicArticleSource
  "PRISMA-informed systematic review of Web of Science and Scopus literature on learning analytics, inclusiveness and students with disabilities; final corpus 26 articles and explicit gaps in attention to disabled and disadvantaged learners."
  Attr.publicAttribution

khalilCandidate : Round6Candidate
khalilCandidate = mkRound6Candidate
  khalilSladePrinslooSource
  "DOI 10.1007/s12528-023-09363-4; PMID 37359042; PMCID PMC10013273 verified"
  disabilityAnalyticsByEvidenceGap
  PhilosophyAudit.philosophyClaimProvenancePromotion
  "High-alpha source for disability/access x analytics evidence absence. It lets the audit distinguish a field's claimed inclusive potential from the actual distribution of research attention across disabled/disadvantaged populations."
  "Systematic-review synthesis of its own 26-item corpus; does not pay this review's search execution, establish intervention effectiveness, or provide disabled students' direct constitutive authority by itself."

------------------------------------------------------------------------
-- Political economy of user data and control.
------------------------------------------------------------------------

komljenovicBirchSellarSource : Attr.AttributedSource
komljenovicBirchSellarSource = Attr.mkDOISource
  "Janja Komljenovic; Kean Birch; Sam Sellar"
  "Monetising Digital Data in Higher Education: Analysing the Strategies and Struggles of EdTech Startups"
  "Postdigital Science and Education 6, 1196-1215"
  "2024"
  "10.1007/s42438-024-00505-0"
  "https://doi.org/10.1007/s42438-024-00505-0"
  Attr.academicArticleSource
  "Empirical three-year UK higher-education EdTech study drawing on startup and university interviews, focus groups and documents; analyses datafication, data products, data externalities, data control/consolidation and economic-value strategies."
  Attr.publicAttribution

komljenovicCandidate : Round6Candidate
komljenovicCandidate = mkRound6Candidate
  komljenovicBirchSellarSource
  "DOI verified; linked UK Data Service research-data DOI 10.5255/UKDA-SN-856729 retained as a distinct dataset identity, not the article identity"
  dataMonetisationByUserControlAndPoliticalEconomy
  PhilosophyAudit.platformInstitutionalPower
  "Direct political-economy donor for student/staff-generated data x firm/university value creation x control/repurposing. The study reports that data can be recombined into metrics, products and externalities while data-producing students/staff may lack control over downstream analytics/products."
  "UK higher-education EdTech startup/university study; does not establish that every platform monetises data, that every data use harms students, or that economic value alone determines educational governance or sustainability."

canonicalRound6Frontier : List Round6Candidate
canonicalRound6Frontier =
  liCandidate
  ∷ bakerHawnCandidate
  ∷ khalilCandidate
  ∷ komljenovicCandidate
  ∷ []

------------------------------------------------------------------------
-- No-promotion / intersectional-exit firewalls.
------------------------------------------------------------------------

data Round6CandidateCreatesIncludedStudy : Set where
data OptOutChoiceImpliesRepresentativeSelection : Set where
data BiasReviewCreatesNamedSystemBiasFinding : Set where
data DisabilityReviewCreatesParticipantAuthority : Set where
data DataMonetisationStudyCreatesUniversalExtractionLaw : Set where
data DatasetDOIEqualsArticleDOI : Set where

round6CandidateDoesNotCreateIncludedStudy : Round6CandidateCreatesIncludedStudy → ⊥
round6CandidateDoesNotCreateIncludedStudy ()

optOutChoiceDoesNotImplyRepresentativeSelection :
  OptOutChoiceImpliesRepresentativeSelection → ⊥
optOutChoiceDoesNotImplyRepresentativeSelection ()

biasReviewDoesNotCreateNamedSystemBiasFinding :
  BiasReviewCreatesNamedSystemBiasFinding → ⊥
biasReviewDoesNotCreateNamedSystemBiasFinding ()

disabilityReviewDoesNotCreateParticipantAuthority :
  DisabilityReviewCreatesParticipantAuthority → ⊥
disabilityReviewDoesNotCreateParticipantAuthority ()

dataMonetisationStudyDoesNotCreateUniversalExtractionLaw :
  DataMonetisationStudyCreatesUniversalExtractionLaw → ⊥
dataMonetisationStudyDoesNotCreateUniversalExtractionLaw ()

datasetDOIDoesNotEqualArticleDOI : DatasetDOIEqualsArticleDOI → ⊥
datasetDOIDoesNotEqualArticleDOI ()
