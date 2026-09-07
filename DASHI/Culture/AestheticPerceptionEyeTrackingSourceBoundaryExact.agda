module DASHI.Culture.AestheticPerceptionEyeTrackingSourceBoundaryExact where

open import DASHI.Core.Prelude
import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- AESTHETIC PERCEPTION / EYE-TRACKING SOURCE BOUNDARY
--
-- Empirical gaze measures are observations of viewer behaviour. They are not
-- definitions of beauty, objective artistic value, institutional status, or
-- market value. Multiple plausible source matches are preserved rather than
-- pretending a vague recollection uniquely identifies one study.
------------------------------------------------------------------------

jankowski2020Source : Source.AttributedSource
jankowski2020Source = Source.mkDOISource
  "Tomasz Jankowski; Piotr Francuz; Piotr Oleś; Elżbieta Chmielnicka-Kuter; Paweł Augustynowicz"
  "The Effect of Painting Beauty on Eye Movements"
  "Advances in Cognitive Psychology 16(3), 213-227" "2020"
  "10.5709/acp-0298-4"
  "https://pmc.ncbi.nlm.nih.gov/articles/PMC7548509/"
  Source.academicArticleSource
  "forty participants viewed and aesthetically evaluated 140 figurative paintings; bounded evidence about relations between evaluation and fixation/viewing structure"
  Source.publicAttribution

mitrovic2020Source : Source.AttributedSource
mitrovic2020Source = Source.mkDOISource
  "Aleksandra Mitrovic; Lisa Mira Hegelmaier; Helmut Leder; Matthew Pelowski"
  "Does beauty capture the eye, even if it's not (overtly) adaptive? A comparative eye-tracking study of spontaneous attention and visual preference with VAST abstract art"
  "Acta Psychologica 209, 103133" "2020"
  "10.1016/j.actpsy.2020.103133"
  "https://pubmed.ncbi.nlm.nih.gov/32717655/"
  Source.academicArticleSource
  "spontaneous looking time was related to later personal preference for abstract designs; the reported relation was not driven by expert-designated quality"
  Source.publicAttribution

data AestheticCoordinate : Set where
  materialArtwork : AestheticCoordinate
  visualFeatures : AestheticCoordinate
  gazeTrajectory : AestheticCoordinate
  fixationDuration : AestheticCoordinate
  spontaneousViewingTime : AestheticCoordinate
  subjectiveLiking expertEvaluation displayContext institutionalArtStatus : AestheticCoordinate
  provenanceHistory marketPrice : AestheticCoordinate

data EvidenceKind : Set where
  eyeTrackingObservation : EvidenceKind
  selfReportEvaluation : EvidenceKind
  expertDesignation : EvidenceKind
  institutionalClassification : EvidenceKind
  provenanceReceipt economicObservation : EvidenceKind

evidenceKind : AestheticCoordinate → EvidenceKind
evidenceKind materialArtwork = provenanceReceipt
evidenceKind visualFeatures = eyeTrackingObservation
evidenceKind gazeTrajectory = eyeTrackingObservation
evidenceKind fixationDuration = eyeTrackingObservation
evidenceKind spontaneousViewingTime = eyeTrackingObservation
evidenceKind subjectiveLiking = selfReportEvaluation
evidenceKind expertEvaluation = expertDesignation
evidenceKind displayContext = institutionalClassification
evidenceKind institutionalArtStatus = institutionalClassification
evidenceKind provenanceHistory = provenanceReceipt
evidenceKind marketPrice = economicObservation

record AestheticEmpiricalReceipt : Set where
  constructor aesthetic-empirical-receipt
  field
    source : Source.AttributedSource
    sample : String
    stimulus : String
    measuredCoordinates : String
    boundedFinding : String
    causalMechanismEstablished : Bool
    objectiveBeautyEstablished : Bool
    marketValueEstablished : Bool

jankowskiReceipt : AestheticEmpiricalReceipt
jankowskiReceipt = aesthetic-empirical-receipt
  jankowski2020Source "40 participants" "140 figurative paintings"
  "eye movements plus aesthetic evaluation; fixation duration, viewing-time window, temporal/spatial attention structure"
  "paintings evaluated as beautiful showed different oculomotor structure; fixations longer than 229 ms were sensitive to evaluation, with a reported effect window roughly 2.3-19.8 seconds"
  false false false

mitrovicReceipt : AestheticEmpiricalReceipt
mitrovicReceipt = aesthetic-empirical-receipt
  mitrovic2020Source "participants viewing paired VAST abstract designs"
  "controlled abstract design pairs"
  "spontaneous looking time followed by preference evaluation"
  "participants looked longer at designs they later personally preferred; the reported effect was driven by personal taste rather than expert-designated objectively better designs"
  false false false

data GazePatternDeterminesObjectiveBeauty : Set where
data LongerLookingMeansObjectiveArtisticValue : Set where
data SubjectiveLikingEqualsMarketValue : Set where
data ExpertDesignationCreatesUniversalBeauty : Set where
data CorrelationProvesCausalAestheticMechanism : Set where
data EyeTrackingExhaustsAestheticExperience : Set where
data InstitutionalStatusDeterminesPersonalLiking : Set where
data PersonalLikingDeterminesInstitutionalStatus : Set where

gazeDoesNotDetermineObjectiveBeauty : GazePatternDeterminesObjectiveBeauty → ⊥
gazeDoesNotDetermineObjectiveBeauty ()
longerLookingDoesNotMeanObjectiveArtisticValue : LongerLookingMeansObjectiveArtisticValue → ⊥
longerLookingDoesNotMeanObjectiveArtisticValue ()
likingDoesNotEqualMarketValue : SubjectiveLikingEqualsMarketValue → ⊥
likingDoesNotEqualMarketValue ()
expertDesignationDoesNotCreateUniversalBeauty : ExpertDesignationCreatesUniversalBeauty → ⊥
expertDesignationDoesNotCreateUniversalBeauty ()
correlationDoesNotProveMechanism : CorrelationProvesCausalAestheticMechanism → ⊥
correlationDoesNotProveMechanism ()
eyeTrackingDoesNotExhaustAestheticExperience : EyeTrackingExhaustsAestheticExperience → ⊥
eyeTrackingDoesNotExhaustAestheticExperience ()
institutionalStatusDoesNotDeterminePersonalLiking : InstitutionalStatusDeterminesPersonalLiking → ⊥
institutionalStatusDoesNotDeterminePersonalLiking ()
personalLikingDoesNotDetermineInstitutionalStatus : PersonalLikingDeterminesInstitutionalStatus → ⊥
personalLikingDoesNotDetermineInstitutionalStatus ()

record AestheticPerceptionEyeTrackingBoundary : Set where
  constructor aesthetic-perception-eye-tracking-boundary
  field
    gazeObservationSeparatedFromJudgment : Bool
    personalLikingSeparatedFromExpertEvaluation : Bool
    personalLikingSeparatedFromMarketValue : Bool
    institutionalStatusSeparatedFromVisualAttention : Bool
    provenanceSeparatedFromVisibleSurface : Bool
    eyeTrackingCorrelationsRecovered : Bool
    objectiveBeautyLawRecovered : Bool
    exhaustiveAestheticMechanismRecovered : Bool
    candidateStudyIdentityUniqueFromVagueMemory : Bool

canonicalAestheticPerceptionEyeTrackingBoundary : AestheticPerceptionEyeTrackingBoundary
canonicalAestheticPerceptionEyeTrackingBoundary =
  aesthetic-perception-eye-tracking-boundary true true true true true true false false false
