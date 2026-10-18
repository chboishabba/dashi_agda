module DASHI.Education.DigitalESDIntersectionalSourceAcquisitionParetoRound17Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Core.IntersectionalNonFactorability as Intersection
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity

------------------------------------------------------------------------
-- ROUND 17: PRE-CARRIER DESIGN EXCLUSION / PROCUREMENT END-USER ABSENCE.
--
-- Post-Round-16 Python recutting left `whoWasExcludedByDesign` and
-- `whoWasAffectedButUnsampled` as the deepest residual pair. Round 17 only
-- admits candidates that expose one of those mechanisms directly.
--
-- Attribution discipline:
--   * article/thesis source roles remain distinct;
--   * a repository Dewey coordinate is navigation only;
--   * ResearchGate artifact identity is not peer-review authority;
--   * external source observations motivate but do not own DASHI finite
--     non-factorability witnesses;
--   * acquisition candidate != final review inclusion.
------------------------------------------------------------------------

data Round17Residual : Set where
  analyticCarrierExcludesNoVideoOrNoWebcamStudents : Round17Residual
  procurementAffectedStudentsWeaklyRepresented : Round17Residual

record Round17Candidate : Set where
  constructor round17-candidate
  field
    source : Attr.AttributedSource
    sourceRoleReceipt : Snowball.SourceRoleSnowballReceipt source
    qidDemand : Identity.ExternalIdentityDemand
    sameObjectExternalIdentityState : String
    deweyState : String
    targetResidual : Round17Residual
    sourceBoundedReading : String
    limitation : String
    includedInFinalCorpus : Bool
    includedInFinalCorpusIsFalse : includedInFinalCorpus ≡ false

open Round17Candidate public

mkRound17Candidate :
  (source : Attr.AttributedSource) →
  String → String → Round17Residual → String → String →
  Round17Candidate
mkRound17Candidate source identityState dewey residual reading limitation =
  round17-candidate
    source
    (Snowball.canonicalSourceRoleSnowballReceipt source)
    (Identity.mkOptionalIdentityDemand
      "DigitalESDIntersectionalSourceAcquisitionParetoRound17Exact"
      (Attr.sourceTitle source)
      (Attr.sourceTitle source)
      Identity.wikidataQid
      (Identity.unresolved "no independently verified same-object publication QID recorded by round 17"))
    identityState
    dewey
    residual reading limitation false refl

------------------------------------------------------------------------
-- Händel et al. 2022: the target survey carrier is narrowed by explicit
-- exclusion rules before webcam-engagement analysis.
------------------------------------------------------------------------

handelWebcamSource : Attr.AttributedSource
handelWebcamSource = Attr.mkDOISource
  "Marion Händel; Svenja Bedenlier; Bärbel Kopp; Michaela Gläser-Zikuda; Rudolf Kammerl; Albert Ziegler"
  "The webcam and student engagement in synchronous online learning: visually or verbally?"
  "Education and Information Technologies 27(7), 10405-10428"
  "2022"
  "10.1007/s10639-022-11050-3"
  "https://doi.org/10.1007/s10639-022-11050-3"
  Attr.academicArticleSource
  "Primary cross-sectional higher-education survey on webcam non/use and synchronous-online engagement. From 4,143 completed surveys, 284 students reporting no videoconference participation and 237 reporting no webcam access were excluded before the 3,610-student analytic sample used for the focal webcam analyses."
  Attr.publicAttribution

handelCandidate : Round17Candidate
handelCandidate = mkRound17Candidate
  handelWebcamSource
  "DOI 10.1007/s10639-022-11050-3; PMID 35464115; PMCID PMC9013737; University of Augsburg OPUS record 96855"
  "Dewey 150 Psychology recorded by the University of Augsburg repository; navigation/classification only, not evidence or authority"
  analyticCarrierExcludesNoVideoOrNoWebcamStudents
  "Direct pre-carrier exclusion witness for the absence audit: students unable to access a webcam and students not participating in videoconferencing are part of the survey-return population but are removed from the focal analytic carrier by the study question/design. The resulting webcam-engagement result therefore cannot silently stand for those excluded groups."
  "The exclusions are appropriate to the paper's focal webcam question and do not by themselves constitute methodological wrongdoing. No webcam access does not imply no educational engagement, and the excluded groups' outcomes cannot be inferred from the retained analytic sample."

------------------------------------------------------------------------
-- Bradstreet 2025 MSc thesis: procurement professionals describe student/end-
-- user participation in UK HE ed-tech procurement.
------------------------------------------------------------------------

bradstreetProcurementThesisSource : Attr.AttributedSource
bradstreetProcurementThesisSource = Attr.mkNoDOISource
  "Alexis Bradstreet"
  "Ethical Ed-tech Procurement in UK Higher Education: Decision-Making, Knowledge Gaps, and Opportunities for Improvement"
  "MSc final project, Data and AI Ethics, Edinburgh Futures Institute, University of Edinburgh; public ResearchGate artifact"
  "2025"
  "https://www.researchgate.net/publication/394926079_Ethical_Ed-tech_Procurement_in_UK_Higher_Education_Decision-Making_Knowledge_Gaps_and_Opportunities_for_Improvement"
  (Attr.namedSourceKind "MSc thesis")
  "Qualitative MSc thesis based on seven UK higher-education procurement professionals. It examines ethical/social/pedagogical trade-offs and reports that educators are more often involved than students in procurement, with legal and practical constraints offered as reasons for weak student involvement."
  Attr.publicAttribution

bradstreetCandidate : Round17Candidate
bradstreetCandidate = mkRound17Candidate
  bradstreetProcurementThesisSource
  "ResearchGate artifact reports identifier 10.13140/RG.2.2.27078.74560; retained here as artifact/navigation metadata rather than a peer-reviewed journal DOI claim"
  "Dewey classification unresolved; no nearest-label substitution"
  procurementAffectedStudentsWeaklyRepresented
  "High-alpha affected-but-unsampled/decision-carrier donor: procurement professionals describe decisions over technologies that affect students while student participation in procurement is reported as comparatively rare. This distinguishes affected end users from the evidence/decision carrier used by procurement practice."
  "MSc thesis with seven procurement-professional interviews, not a peer-reviewed sector-wide prevalence study. Procurement-professional accounts do not create student testimony, equal decision authority, product-level harms, or a universal UK HE procurement law."

canonicalRound17Frontier : List Round17Candidate
canonicalRound17Frontier = handelCandidate ∷ bradstreetCandidate ∷ []

------------------------------------------------------------------------
-- DASHI-owned collision 1: the same retained analytic sample can coexist with
-- materially different excluded populations. The retained carrier alone cannot
-- recover the excluded-population state required by the absence consumer.
------------------------------------------------------------------------

data ExcludedCarrierWorld : Set where
  sameAnalyticCarrierSmallExcludedPopulation : ExcludedCarrierWorld
  sameAnalyticCarrierLargeExcludedPopulation : ExcludedCarrierWorld

data AnalyticSampleSurface : Set where
  sameRetainedAnalyticSample : AnalyticSampleSurface

analyticSampleProjection : ExcludedCarrierWorld → AnalyticSampleSurface
analyticSampleProjection sameAnalyticCarrierSmallExcludedPopulation = sameRetainedAnalyticSample
analyticSampleProjection sameAnalyticCarrierLargeExcludedPopulation = sameRetainedAnalyticSample

excludedPopulationMaterial : ExcludedCarrierWorld → Bool
excludedPopulationMaterial sameAnalyticCarrierSmallExcludedPopulation = false
excludedPopulationMaterial sameAnalyticCarrierLargeExcludedPopulation = true

excludedPopulationDiffers :
  excludedPopulationMaterial sameAnalyticCarrierSmallExcludedPopulation ≡
  excludedPopulationMaterial sameAnalyticCarrierLargeExcludedPopulation → ⊥
excludedPopulationDiffers ()

excludedCarrierWitness :
  Intersection.NonFactorabilityWitness analyticSampleProjection excludedPopulationMaterial
excludedCarrierWitness =
  Intersection.nonFactorabilityWitness
    sameAnalyticCarrierSmallExcludedPopulation
    sameAnalyticCarrierLargeExcludedPopulation
    refl excludedPopulationDiffers

ExcludedCarrierFactorisation : Set₁
ExcludedCarrierFactorisation =
  Intersection.FactorsThrough analyticSampleProjection excludedPopulationMaterial

excludedCarrierDoesNotFactorThroughAnalyticSample :
  ExcludedCarrierFactorisation → ⊥
excludedCarrierDoesNotFactorThroughAnalyticSample =
  Intersection.witnessRulesOutEveryFlatFactorisation excludedCarrierWitness

------------------------------------------------------------------------
-- DASHI-owned collision 2: the same procurement-professional surface can
-- coexist with materially different student/end-user decision participation.
------------------------------------------------------------------------

data ProcurementDecisionWorld : Set where
  sameProcurementSurfaceStudentIncluded : ProcurementDecisionWorld
  sameProcurementSurfaceStudentExcluded : ProcurementDecisionWorld

data ProcurementProfessionalSurface : Set where
  sameProcurementProfessionalEvidence : ProcurementProfessionalSurface

procurementSurfaceProjection : ProcurementDecisionWorld → ProcurementProfessionalSurface
procurementSurfaceProjection sameProcurementSurfaceStudentIncluded = sameProcurementProfessionalEvidence
procurementSurfaceProjection sameProcurementSurfaceStudentExcluded = sameProcurementProfessionalEvidence

studentDecisionParticipation : ProcurementDecisionWorld → Bool
studentDecisionParticipation sameProcurementSurfaceStudentIncluded = true
studentDecisionParticipation sameProcurementSurfaceStudentExcluded = false

studentDecisionParticipationDiffers :
  studentDecisionParticipation sameProcurementSurfaceStudentIncluded ≡
  studentDecisionParticipation sameProcurementSurfaceStudentExcluded → ⊥
studentDecisionParticipationDiffers ()

decisionCarrierWitness :
  Intersection.NonFactorabilityWitness procurementSurfaceProjection studentDecisionParticipation
decisionCarrierWitness =
  Intersection.nonFactorabilityWitness
    sameProcurementSurfaceStudentIncluded
    sameProcurementSurfaceStudentExcluded
    refl studentDecisionParticipationDiffers

DecisionCarrierFactorisation : Set₁
DecisionCarrierFactorisation =
  Intersection.FactorsThrough procurementSurfaceProjection studentDecisionParticipation

decisionCarrierDoesNotFactorThroughProcurementSurface :
  DecisionCarrierFactorisation → ⊥
decisionCarrierDoesNotFactorThroughProcurementSurface =
  Intersection.witnessRulesOutEveryFlatFactorisation decisionCarrierWitness

------------------------------------------------------------------------
-- No-promotion / source-role firewalls.
------------------------------------------------------------------------

data Round17CandidateCreatesIncludedStudy : Set where
data AnalyticExclusionCreatesPopulationAbsence : Set where
data NoWebcamCreatesNoEngagement : Set where
data ProcurementProfessionalEvidenceCreatesStudentAuthority : Set where
data ThesisCreatesPeerReviewedArticleAuthority : Set where

round17CandidateDoesNotCreateIncludedStudy :
  Round17CandidateCreatesIncludedStudy → ⊥
round17CandidateDoesNotCreateIncludedStudy ()

analyticExclusionDoesNotCreatePopulationAbsence :
  AnalyticExclusionCreatesPopulationAbsence → ⊥
analyticExclusionDoesNotCreatePopulationAbsence ()

noWebcamDoesNotCreateNoEngagement : NoWebcamCreatesNoEngagement → ⊥
noWebcamDoesNotCreateNoEngagement ()

procurementProfessionalEvidenceDoesNotCreateStudentAuthority :
  ProcurementProfessionalEvidenceCreatesStudentAuthority → ⊥
procurementProfessionalEvidenceDoesNotCreateStudentAuthority ()

thesisDoesNotCreatePeerReviewedArticleAuthority :
  ThesisCreatesPeerReviewedArticleAuthority → ⊥
thesisDoesNotCreatePeerReviewedArticleAuthority ()

round17Reading : String
round17Reading =
  "Round 17 follows the post-Round-16 P0 residuals instead of acquiring another broad inclusion paper. Händel et al. explicitly remove students with no videoconference participation or no webcam access before the focal webcam-engagement analytic carrier; Bradstreet's MSc thesis reports comparatively weak student involvement in UK higher-education ed-tech procurement from procurement-professional interviews. DASHI separately owns finite witnesses that a retained analytic sample cannot recover the excluded-population state and a procurement-professional evidence surface cannot recover student/end-user decision participation. Source type, DOI/artifact identifiers, Dewey navigation and acquisition priority create no corpus inclusion or authority."
