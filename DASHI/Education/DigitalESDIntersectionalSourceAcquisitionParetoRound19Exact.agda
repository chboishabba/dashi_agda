module DASHI.Education.DigitalESDIntersectionalSourceAcquisitionParetoRound19Exact where

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
-- ROUND 19: NONRESPONSE / REALISED-CARRIER VALIDATION.
--
-- Post-Round-18 Python recutting leaves `whoWasExcludedByDesign` and
-- `whoWasEligibleButMissing` as P0 residuals. This round targets same-object
-- evidence that can inspect or experimentally perturb the missing carrier
-- instead of treating nonresponse as an unobserved residual.
------------------------------------------------------------------------

data Round19Residual : Set where
  studentSurveyNonresponseByAdministrativeValidation : Round19Residual
  assessmentModeByParticipationAndSelection : Round19Residual

record Round19Candidate : Set where
  constructor round19-candidate
  field
    source : Attr.AttributedSource
    sourceRoleReceipt : Snowball.SourceRoleSnowballReceipt source
    qidDemand : Identity.ExternalIdentityDemand
    deweyState : String
    targetResidual : Round19Residual
    sourceBoundedReading : String
    limitation : String
    includedInFinalCorpus : Bool
    includedInFinalCorpusIsFalse : includedInFinalCorpus ≡ false

open Round19Candidate public

mkRound19Candidate :
  (source : Attr.AttributedSource) →
  Round19Residual → String → String →
  Round19Candidate
mkRound19Candidate source residual reading limitation =
  round19-candidate
    source
    (Snowball.canonicalSourceRoleSnowballReceipt source)
    (Identity.mkOptionalIdentityDemand
      "DigitalESDIntersectionalSourceAcquisitionParetoRound19Exact"
      (Attr.sourceTitle source)
      (Attr.sourceTitle source)
      Identity.wikidataQid
      (Identity.unresolved "no independently verified same-object publication QID recorded by round 19"))
    "Dewey classification unresolved; no nearest-label substitution"
    residual reading limitation false refl

------------------------------------------------------------------------
-- Standish/Umbach 2019: respondents vs nonrespondents validated against
-- corresponding administrative behaviour.
------------------------------------------------------------------------

standishUmbachNonresponseSource : Attr.AttributedSource
standishUmbachNonresponseSource = Attr.mkDOISource
  "Trey Standish; Paul D. Umbach"
  "Should We Be Concerned About Nonresponse Bias in College Student Surveys? Evidence of Bias from a Validation Study"
  "Research in Higher Education 60(3), 338-357"
  "2019"
  "10.1007/s11162-018-9530-2"
  "https://doi.org/10.1007/s11162-018-9530-2"
  Attr.academicArticleSource
  "College-student survey validation study linking survey response status to corresponding administrative measures of campus recreation use, academic performance, physical-education attendance and co-curricular participation. The study reports topic-related response propensity and statistically significant respondent/nonrespondent behavioural differences for 11 of 13 survey questions."
  Attr.publicAttribution

standishCandidate : Round19Candidate
standishCandidate = mkRound19Candidate
  standishUmbachNonresponseSource
  studentSurveyNonresponseByAdministrativeValidation
  "Direct same-object P0 donor for eligible-but-missing: nonrespondents are not merely an inferred blank category because administrative records permit behavioural comparison with respondents. The respondent survey surface therefore cannot automatically stand for the target student population."
  "Specific institutional survey topics and administrative measures. Nonresponse differences do not imply every student survey is biased, do not recover nonrespondents' unmeasured testimony, and do not make administrative data a complete representation of student experience."

------------------------------------------------------------------------
-- Zinn/Landrock/Gnambs 2021: randomized assessment mode changes realised
-- participation carrier and permits explicit study of mode-specific nonresponse.
------------------------------------------------------------------------

zinnLandrockGnambsModeSource : Attr.AttributedSource
zinnLandrockGnambsModeSource = Attr.mkDOISource
  "Sabine Zinn; Uta Landrock; Timo Gnambs"
  "Web-based and mixed-mode cognitive large-scale assessments in higher education: An evaluation of selection bias, measurement bias, and prediction bias"
  "Behavior Research Methods 53, 1202-1217"
  "2021"
  "10.3758/s13428-020-01480-7"
  "https://doi.org/10.3758/s13428-020-01480-7"
  Attr.academicArticleSource
  "Experimental higher-education assessment study using 17,473 German National Educational Panel Study students randomly assigned to supervised paper, supervised computer or unsupervised web testing. It explicitly models mode-specific participation/nonresponse and subsequently invites 6,804 supervised-mode nonresponders to web testing, separating selection, measurement and prediction bias questions."
  Attr.publicAttribution

zinnCandidate : Round19Candidate
zinnCandidate = mkRound19Candidate
  zinnLandrockGnambsModeSource
  assessmentModeByParticipationAndSelection
  "Strong dual-P0 donor: the measurement mode is itself part of the participation design, and the realised carrier differs across assigned modes. Switching supervised-mode nonresponders to a flexible web mode makes otherwise-missing participation empirically inspectable instead of assuming assigned mode produces an equivalent sample."
  "One large-scale German scientific-literacy assessment context. Higher web response does not prove absence of selection, measurement or prediction bias; reported generally small bias does not establish equivalence for every construct, population or digital-education setting."

canonicalRound19Frontier : List Round19Candidate
canonicalRound19Frontier = zinnCandidate ∷ standishCandidate ∷ []

------------------------------------------------------------------------
-- DASHI collision 1: the same observed respondent survey surface may coexist
-- with different nonrespondent behaviour. Therefore respondent-only data cannot
-- recover the missing-population state required by the consumer.
------------------------------------------------------------------------

data RespondentCarrierWorld : Set where
  sameSurveySurfaceNonrespondentsSimilar : RespondentCarrierWorld
  sameSurveySurfaceNonrespondentsDifferent : RespondentCarrierWorld

data ObservedSurveySurface : Set where
  sameRespondentSurvey : ObservedSurveySurface

observedSurveyProjection : RespondentCarrierWorld → ObservedSurveySurface
observedSurveyProjection sameSurveySurfaceNonrespondentsSimilar = sameRespondentSurvey
observedSurveyProjection sameSurveySurfaceNonrespondentsDifferent = sameRespondentSurvey

nonrespondentBehaviourMateriallyDiffers : RespondentCarrierWorld → Bool
nonrespondentBehaviourMateriallyDiffers sameSurveySurfaceNonrespondentsSimilar = false
nonrespondentBehaviourMateriallyDiffers sameSurveySurfaceNonrespondentsDifferent = true

nonrespondentBehaviourReallyDiffers :
  nonrespondentBehaviourMateriallyDiffers sameSurveySurfaceNonrespondentsSimilar ≡
  nonrespondentBehaviourMateriallyDiffers sameSurveySurfaceNonrespondentsDifferent → ⊥
nonrespondentBehaviourReallyDiffers ()

respondentCarrierWitness :
  Intersection.NonFactorabilityWitness observedSurveyProjection nonrespondentBehaviourMateriallyDiffers
respondentCarrierWitness =
  Intersection.nonFactorabilityWitness
    sameSurveySurfaceNonrespondentsSimilar
    sameSurveySurfaceNonrespondentsDifferent
    refl nonrespondentBehaviourReallyDiffers

RespondentCarrierFactorisation : Set
RespondentCarrierFactorisation =
  Intersection.FactorsThrough observedSurveyProjection nonrespondentBehaviourMateriallyDiffers

respondentCarrierDoesNotFactorThroughObservedSurveySurface :
  RespondentCarrierFactorisation → ⊥
respondentCarrierDoesNotFactorThroughObservedSurveySurface =
  Intersection.witnessRulesOutEveryFlatFactorisation respondentCarrierWitness

------------------------------------------------------------------------
-- DASHI collision 2: the same formal assigned-mode label can coexist with
-- different realised participation states. Assignment alone cannot recover the
-- carrier actually observed by the study.
------------------------------------------------------------------------

data ModeParticipationWorld : Set where
  assignedModeHighParticipation : ModeParticipationWorld
  assignedModeLowParticipation : ModeParticipationWorld

data AssignedModeSurface : Set where
  sameFormalAssignedMode : AssignedModeSurface

assignedModeProjection : ModeParticipationWorld → AssignedModeSurface
assignedModeProjection assignedModeHighParticipation = sameFormalAssignedMode
assignedModeProjection assignedModeLowParticipation = sameFormalAssignedMode

realisedParticipationAdequate : ModeParticipationWorld → Bool
realisedParticipationAdequate assignedModeHighParticipation = true
realisedParticipationAdequate assignedModeLowParticipation = false

realisedParticipationDiffers :
  realisedParticipationAdequate assignedModeHighParticipation ≡
  realisedParticipationAdequate assignedModeLowParticipation → ⊥
realisedParticipationDiffers ()

modeParticipationWitness :
  Intersection.NonFactorabilityWitness assignedModeProjection realisedParticipationAdequate
modeParticipationWitness =
  Intersection.nonFactorabilityWitness
    assignedModeHighParticipation
    assignedModeLowParticipation
    refl realisedParticipationDiffers

ModeParticipationFactorisation : Set
ModeParticipationFactorisation =
  Intersection.FactorsThrough assignedModeProjection realisedParticipationAdequate

modeParticipationDoesNotFactorThroughAssignedModeSurface :
  ModeParticipationFactorisation → ⊥
modeParticipationDoesNotFactorThroughAssignedModeSurface =
  Intersection.witnessRulesOutEveryFlatFactorisation modeParticipationWitness

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data Round19CandidateCreatesIncludedStudy : Set where
data RespondentSurfaceCreatesNonrespondentBehaviour : Set where
data ResponsePropensityCreatesPopulationTruth : Set where
data AssignedModeCreatesRealisedCarrierEquivalence : Set where
data HigherResponseRateCreatesNoSelectionBias : Set where

round19CandidateDoesNotCreateIncludedStudy : Round19CandidateCreatesIncludedStudy → ⊥
round19CandidateDoesNotCreateIncludedStudy ()

respondentSurfaceDoesNotCreateNonrespondentBehaviour :
  RespondentSurfaceCreatesNonrespondentBehaviour → ⊥
respondentSurfaceDoesNotCreateNonrespondentBehaviour ()

responsePropensityDoesNotCreatePopulationTruth :
  ResponsePropensityCreatesPopulationTruth → ⊥
responsePropensityDoesNotCreatePopulationTruth ()

assignedModeDoesNotCreateRealisedCarrierEquivalence :
  AssignedModeCreatesRealisedCarrierEquivalence → ⊥
assignedModeDoesNotCreateRealisedCarrierEquivalence ()

higherResponseRateDoesNotCreateNoSelectionBias :
  HigherResponseRateCreatesNoSelectionBias → ⊥
higherResponseRateDoesNotCreateNoSelectionBias ()

round19Reading : String
round19Reading =
  "Round 19 follows the residual matrix to same-object nonresponse evidence. Standish/Umbach compare survey respondents and nonrespondents through corresponding administrative behaviour; Zinn/Landrock/Gnambs experimentally vary assessment mode and observe mode-specific participation/nonresponse, including supervised-mode nonresponders subsequently offered web testing. DASHI separately owns finite witnesses showing that a respondent-only survey surface cannot recover nonrespondent behaviour and formal assigned mode cannot recover the realised participant carrier. Neither source is thereby included in the final Digital-ESD corpus."
