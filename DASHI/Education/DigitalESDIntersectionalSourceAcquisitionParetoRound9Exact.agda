module DASHI.Education.DigitalESDIntersectionalSourceAcquisitionParetoRound9Exact where

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
-- ROUND 9: INTERSECTIONAL FLAGGING / DISABILITY SURVEILLANCE / ADOPTION POWER.
--
-- Python coverage audit over rounds 1--8 identified the sparsest current
-- absence-audit fibres as:
--   * whose future options are affected;
--   * who is excluded by design;
--   * who defines the categories/classifications;
--   * who is eligible but missing;
--   * who must disclose to become visible.
--
-- Round 9 therefore targets sources that jointly discriminate surveillance,
-- disability/race/sex, algorithmic flagging and institutional adoption power.
-- Candidate acquisition != corpus inclusion.
------------------------------------------------------------------------

data Round9Residual : Set where
  intersectionalProctorFlagging : Round9Residual
  disabilityWrongfulFlagStakes : Round9Residual
  studentExclusionFromInstitutionalAdoption : Round9Residual
  disabilityPrivacyAccommodationTradeoff : Round9Residual

record Round9Candidate : Set where
  constructor round9-candidate
  field
    source : Attr.AttributedSource
    sourceRoleReceipt : Snowball.SourceRoleSnowballReceipt source
    qidDemand : Identity.ExternalIdentityDemand
    targetResidual : Round9Residual
    auditLens : PhilosophyAudit.PhilosophyAuditFamily
    sourceBoundedReading : String
    limitation : String
    includedInFinalCorpus : Bool
    includedInFinalCorpusIsFalse : includedInFinalCorpus ≡ false

open Round9Candidate public

mkRound9Candidate :
  (source : Attr.AttributedSource) →
  Round9Residual →
  PhilosophyAudit.PhilosophyAuditFamily →
  String →
  String →
  Round9Candidate
mkRound9Candidate source residual lens reading limitation =
  round9-candidate
    source
    (Snowball.canonicalSourceRoleSnowballReceipt source)
    (Identity.mkOptionalIdentityDemand
      "DigitalESDIntersectionalSourceAcquisitionParetoRound9Exact"
      (Attr.sourceTitle source)
      (Attr.sourceTitle source)
      Identity.wikidataQid
      (Identity.unresolved "no independently verified same-object article QID recorded by round 9"))
    residual lens reading limitation false refl

------------------------------------------------------------------------
-- Quantified race x skin-tone x sex disparity in automated proctor flags.
------------------------------------------------------------------------

yoderHimesEtAlSource : Attr.AttributedSource
yoderHimesEtAlSource = Attr.mkDOISource
  "Deborah R. Yoder-Himes; Alina Asif; Kaelin Kinney; Tiffany J. Brandt; Rhiannon E. Cecil; Paul R. Himes; Cara Cashon; Rachel M. P. Hopp; Edna Ross"
  "Racial, skin tone, and sex disparities in automated proctoring software"
  "Frontiers in Education 7"
  "2022"
  "10.3389/feduc.2022.881449"
  "https://doi.org/10.3389/feduc.2022.881449"
  Attr.academicArticleSource
  "Original higher-education study of approximately 357 students across four STEM courses. Instructor-facing automated-proctoring outputs were compared by self-reported race, manually coded skin tone and sex. Black students and students with darker skin tones were flagged more often; women with the darkest skin tones showed an intersectional disparity. The authors separately inspected videos and did not observe corresponding group differences in cheating behaviours."
  Attr.publicAttribution

yoderHimesCandidate : Round9Candidate
yoderHimesCandidate = mkRound9Candidate
  yoderHimesEtAlSource
  intersectionalProctorFlagging
  PhilosophyAudit.antiPanopticonVisibilityAuthority
  "Direct same-system quantitative evidence that an automated proctoring classification surface can distribute review/flag burden differently across race/skin-tone/sex intersections. This is substantially stronger for the current hyperfabric than another generic algorithmic-bias review."
  "Single institutional software deployment and course set; instructor-report outputs rather than first-person student experience. The disparity does not establish universal proctoring bias, intent, actual cheating differences, or downstream disciplinary penalties."

------------------------------------------------------------------------
-- Disabled students, wrongful-flag fear and assessment/career stakes.
------------------------------------------------------------------------

pokornyEtAlSource : Attr.AttributedSource
pokornyEtAlSource = Attr.mkDOISource
  "Annika Pokorny; Cissy J. Ballen; Abby Grace Drake; Emily P. Driessen; Sheritta Fagbodun; Brian Gibbens; Jeremiah A. Henning; Sophie J. McCoy; Seth K. Thompson; Charles G. Willis; A. Kelly Lane"
  "Out of my control: science undergraduates report mental health concerns and inconsistent conditions when using remote proctoring software"
  "International Journal for Educational Integrity 19, 22"
  "2023"
  "10.1007/s40979-023-00141-4"
  "https://doi.org/10.1007/s40979-023-00141-4"
  Attr.academicArticleSource
  "Multi-institutional survey across 11 undergraduate science courses at three US public research institutions. Students reported technological difficulties, fear of wrongful cheating accusations, mental-health effects and suboptimal testing environments. Students mentioning disability/medical/mental-health concerns described additional burdens, including fear that movement or accommodation needs could be flagged and that grades, GPA or careers could be affected."
  Attr.publicAttribution

pokornyCandidate : Round9Candidate
pokornyCandidate = mkRound9Candidate
  pokornyEtAlSource
  disabilityWrongfulFlagStakes
  PhilosophyAudit.antiPanopticonVisibilityAuthority
  "High-alpha disability x surveillance x future-options source: the monitored assessment environment changes cognitive/mental-health burden and students explicitly connect possible misclassification to academic and career consequences."
  "Student-reported concerns and experiences are not an observed administrative-appeal dataset and do not show that feared penalties were actually imposed. Disability categories are heterogeneous and should not be collapsed into one impairment profile."

------------------------------------------------------------------------
-- Institutional adoption authority with students structurally missing.
------------------------------------------------------------------------

shiojiEtAlSource : Attr.AttributedSource
shiojiEtAlSource = Attr.mkDOISource
  "Elisa Shioji; Ani Meliksetyan; Lucy Simko; Ryan Watkins; Adam J. Aviv; Shaanan Cohney"
  "It's been Lovely Watching you: Institutional Decision-Making on Online Proctoring Software"
  "2025 IEEE Symposium on Security and Privacy"
  "2025"
  "10.1109/SP61157.2025.00018"
  "https://doi.org/10.1109/SP61157.2025.00018"
  Attr.academicArticleSource
  "Interview study with 20 university administrators in the United States and Australia examining central adoption or rejection of remote proctoring software. Governance processes included senior administrators, legal and IT actors, while students were sometimes structurally excluded from adoption decisions. Privacy, security, ethics, cost and long-term operational concerns were weighed against academic-integrity goals."
  Attr.publicAttribution

shiojiCandidate : Round9Candidate
shiojiCandidate = mkRound9Candidate
  shiojiEtAlSource
  studentExclusionFromInstitutionalAdoption
  PhilosophyAudit.platformInstitutionalPower
  "Direct 'who defined and decided?' acquisition source: it observes the institutional adoption process itself and identifies cases where affected students were outside the decision table while administrators/legal/IT actors retained decision power."
  "Administrator interviews do not create student voice, prove every adoption process excludes students, or establish downstream student harm in a named deployment."

------------------------------------------------------------------------
-- First-hand disabled-student surveillance/privacy/accommodation trade-offs.
------------------------------------------------------------------------

kwapiszEtAlSource : Attr.AttributedSource
kwapiszEtAlSource = Attr.mkDOISource
  "Monika Blue Kwapisz; Yoav Ackerman; Jennifer Nguyen; Prashanth Rajivan"
  "Surveillance and Disability in Online Proctored Exams: Student Perspectives and Design Implications"
  "arXiv preprint 2511.10826"
  "2025"
  "10.48550/arXiv.2511.10826"
  "https://doi.org/10.48550/arXiv.2511.10826"
  Attr.academicArticleSource
  "Preprint reporting reflexive thematic analysis of interviews with students who had first-hand online-invigilated-exam experience and disability accommodations. Participants described surveillance/disability interactions, fear of misrepresentation, increased cognitive load, privacy compromises and accommodation trade-offs."
  Attr.publicAttribution

kwapiszCandidate : Round9Candidate
kwapiszCandidate = mkRound9Candidate
  kwapiszEtAlSource
  disabilityPrivacyAccommodationTradeoff
  PhilosophyAudit.antiPanopticonVisibilityAuthority
  "Direct disabled-student observer for surveillance x privacy x accommodation x misrepresentation. It materially sharpens the prior review/institutional evidence because the affected students themselves describe the trade-offs."
  "Preprint status is retained explicitly; it does not receive peer-reviewed-source authority. Interview findings do not estimate prevalence, universal disability effects or actual disciplinary outcomes."

canonicalRound9Frontier : List Round9Candidate
canonicalRound9Frontier =
  yoderHimesCandidate
  ∷ pokornyCandidate
  ∷ shiojiCandidate
  ∷ kwapiszCandidate
  ∷ []

------------------------------------------------------------------------
-- No-promotion / observer firewalls.
------------------------------------------------------------------------

data Round9CandidateCreatesIncludedStudy : Set where
data IntersectionalFlagDisparityCreatesCheatingDifference : Set where
data WrongfulFlagFearCreatesObservedPenalty : Set where
data StudentExclusionFromAdoptionCreatesStudentAuthority : Set where
data PreprintCreatesPeerReviewedAuthority : Set where

round9CandidateDoesNotCreateIncludedStudy : Round9CandidateCreatesIncludedStudy → ⊥
round9CandidateDoesNotCreateIncludedStudy ()

intersectionalFlagDisparityDoesNotCreateCheatingDifference :
  IntersectionalFlagDisparityCreatesCheatingDifference → ⊥
intersectionalFlagDisparityDoesNotCreateCheatingDifference ()

wrongfulFlagFearDoesNotCreateObservedPenalty :
  WrongfulFlagFearCreatesObservedPenalty → ⊥
wrongfulFlagFearDoesNotCreateObservedPenalty ()

studentExclusionDoesNotCreateStudentAuthority :
  StudentExclusionFromAdoptionCreatesStudentAuthority → ⊥
studentExclusionDoesNotCreateStudentAuthority ()

preprintDoesNotCreatePeerReviewedAuthority :
  PreprintCreatesPeerReviewedAuthority → ⊥
preprintDoesNotCreatePeerReviewedAuthority ()
