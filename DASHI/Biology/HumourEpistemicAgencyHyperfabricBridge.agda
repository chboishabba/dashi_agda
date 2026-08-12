module DASHI.Biology.HumourEpistemicAgencyHyperfabricBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Biology.HumourOnlineEngagementFramework as Humour
import DASHI.Biology.OEFMultiFibreFeedbackHyperfabric as OEF
import DASHI.Biology.StudentVoiceEpistemicAgencyBridge as Voice
import DASHI.Core.AdmissibleReachability as Reachability
import DASHI.Core.ConditionalNormalizationBoundary as Conditional
import DASHI.Core.DynamicalQuotientSafety as Dynamic
import DASHI.Core.EpistemicInquiryGovernance as Governance
import DASHI.Core.PluralConsumerProjectionSafety as Plural
import DASHI.Core.TypedDependencyCore as Dependency
import DASHI.Reasoning.DialecticInvariantGeometry as Dialectic

------------------------------------------------------------------------
-- CROSS-PAPER / DASHI FORMAL EXTENSION
--
-- Source anchors:
--
--   Alice Brown, Josephine Pryce, Anja Pabel (2025),
--   "Considerations for integrating humour as a strategy to heighten online
--   student engagement and learning in higher education: An emerging
--   framework", HERDSA Conference, p. 64. DOI: no DOI assigned/listed.
--
--   Alice Brown and Megan Kimber (2026),
--   "Repositioning Student Voice and Agency: A Call for the Epistemic
--   Expansion of Scholarship of Teaching and Learning Inquiry",
--   Active Learning in Higher Education 27(2), 253-264.
--   DOI: 10.1177/14697874261426374.
--
-- Intersectional reference / motivation:
--   Kimberle Crenshaw (1989), "Demarginalizing the Intersection of Race and
--   Sex", University of Chicago Legal Forum 1989(1), Article 8.
--   DOI: no DOI assigned to the original article.
--
-- These sources motivate the domain interpretation.  The typed governance,
-- carrier-expansion, plural-safety and dynamic-defect constructions below are
-- DASHI formal extensions and are not attributed as theorems of those papers.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Brown/Kimber participation stages as constitutive-governance coordinates.
--
-- Feedback alone supplies no constructor here.  Higher stages gain explicitly
-- scoped authority over the inquiry coordinates they can contest or revise.
------------------------------------------------------------------------

data StageAuthorises :
    Voice.EpistemicParticipationStage →
    Governance.InquiryCoordinate → Set where
  questionShapesConsumer :
    StageAuthorises
      Voice.questionContributorStage
      Governance.consumerCoordinate

  codingShapesProjection :
    StageAuthorises
      Voice.codingFrameContributorStage
      Governance.projectionCoordinate

  interpretationShapesRelevance :
    StageAuthorises
      Voice.coInterpreterStage
      Governance.relevanceCoordinate

  coDesignShapesCarrier :
    StageAuthorises
      Voice.coDesignerStage
      Governance.carrierCoordinate

  coDesignShapesProjection :
    StageAuthorises
      Voice.coDesignerStage
      Governance.projectionCoordinate

  coDesignShapesDynamics :
    StageAuthorises
      Voice.coDesignerStage
      Governance.dynamicsCoordinate

  evidenceReviewShapesResidual :
    StageAuthorises
      Voice.evidenceReturnReviewerStage
      Governance.residualCoordinate

  evidenceReviewShapesRevision :
    StageAuthorises
      Voice.evidenceReturnReviewerStage
      Governance.revisionCoordinate

humourStageGovernance :
  Governance.EpistemicGovernance Voice.EpistemicParticipationStage
humourStageGovernance = Governance.epistemicGovernance StageAuthorises

feedbackStageHasNoConstitutiveAuthority :
  (coordinate : Governance.InquiryCoordinate) →
  StageAuthorises Voice.feedbackSourceStage coordinate →
  ⊥
feedbackStageHasNoConstitutiveAuthority coordinate ()

questionContributionCanShapeConsumer :
  Governance.Authorised humourStageGovernance
    Voice.questionContributorStage Governance.consumerCoordinate
questionContributionCanShapeConsumer = questionShapesConsumer

codingContributionCanContestProjection :
  Governance.Authorised humourStageGovernance
    Voice.codingFrameContributorStage Governance.projectionCoordinate
codingContributionCanContestProjection = codingShapesProjection

------------------------------------------------------------------------
-- Intersectionality as strict carrier expansion, not merely reweighting.
------------------------------------------------------------------------

data FlatAudienceAxis : Set where
  ageAxis cultureAxis languageAxis : FlatAudienceAxis

data SituatedAudienceAxis : Set where
  situatedAgeAxis : SituatedAudienceAxis
  situatedCultureAxis : SituatedAudienceAxis
  situatedLanguageAxis : SituatedAudienceAxis
  raceAxis : SituatedAudienceAxis
  classAxis : SituatedAudienceAxis
  genderAxis : SituatedAudienceAxis
  disabilityAxis : SituatedAudienceAxis
  neurotypeAxis : SituatedAudienceAxis
  caringRoleAxis : SituatedAudienceAxis
  institutionalPowerAxis : SituatedAudienceAxis
  historicalContextAxis : SituatedAudienceAxis

embedFlatAudienceAxis : FlatAudienceAxis → SituatedAudienceAxis
embedFlatAudienceAxis ageAxis = situatedAgeAxis
embedFlatAudienceAxis cultureAxis = situatedCultureAxis
embedFlatAudienceAxis languageAxis = situatedLanguageAxis

institutionalPowerHasNoFlatPreimage :
  (axis : FlatAudienceAxis) →
  embedFlatAudienceAxis axis ≡ institutionalPowerAxis →
  ⊥
institutionalPowerHasNoFlatPreimage ageAxis ()
institutionalPowerHasNoFlatPreimage cultureAxis ()
institutionalPowerHasNoFlatPreimage languageAxis ()

historicalContextHasNoFlatPreimage :
  (axis : FlatAudienceAxis) →
  embedFlatAudienceAxis axis ≡ historicalContextAxis →
  ⊥
historicalContextHasNoFlatPreimage ageAxis ()
historicalContextHasNoFlatPreimage cultureAxis ()
historicalContextHasNoFlatPreimage languageAxis ()

------------------------------------------------------------------------
-- Situated humour as dynamics.
--
-- Two students can have the same present positive observable while the same
-- later admissible interaction separates their consumer-visible futures.
------------------------------------------------------------------------

data HumourStudentState : Set where
  visibleLaughTrust : HumourStudentState
  visibleLaughMasking : HumourStudentState
  laterTrust : HumourStudentState
  laterWithdrawal : HumourStudentState

data HumourAction : Set where
  subsequentClassInteraction : HumourAction

data HumourPrecondition : HumourStudentState → HumourAction → Set where
  trustReady :
    HumourPrecondition visibleLaughTrust subsequentClassInteraction
  maskingReady :
    HumourPrecondition visibleLaughMasking subsequentClassInteraction

data HumourPostcondition :
    HumourStudentState → HumourAction → HumourStudentState → Set where
  trustContinues :
    HumourPostcondition
      visibleLaughTrust subsequentClassInteraction laterTrust
  maskingWithdraws :
    HumourPostcondition
      visibleLaughMasking subsequentClassInteraction laterWithdrawal

humourActionLabel : HumourAction → String
humourActionLabel subsequentClassInteraction =
  "subsequent classroom interaction after currently positive visible reception"

humourSystem :
  Dependency.DependentActionSystem HumourStudentState HumourAction
humourSystem = record
  { Precondition = HumourPrecondition
  ; Postcondition = HumourPostcondition
  ; actionLabel = humourActionLabel
  }

trustAdvance :
  Dependency.AdmissibleAction
    humourSystem visibleLaughTrust subsequentClassInteraction
trustAdvance = record
  { precondition = trustReady
  ; after = laterTrust
  ; postcondition = trustContinues
  ; dependencyReceipt = "trust-bearing state advances to later trust"
  }

maskingAdvance :
  Dependency.AdmissibleAction
    humourSystem visibleLaughMasking subsequentClassInteraction
maskingAdvance = record
  { precondition = maskingReady
  ; after = laterWithdrawal
  ; postcondition = maskingWithdraws
  ; dependencyReceipt = "masking/compliance state advances to later withdrawal"
  }

trustExecution :
  Reachability.Executes humourSystem
    (subsequentClassInteraction ∷ [])
    visibleLaughTrust
    laterTrust
trustExecution =
  Reachability.executesCons trustAdvance Reachability.executesNil

maskingExecution :
  Reachability.Executes humourSystem
    (subsequentClassInteraction ∷ [])
    visibleLaughMasking
    laterWithdrawal
maskingExecution =
  Reachability.executesCons maskingAdvance Reachability.executesNil


data HumourConsumer : Set where
  threeCsConsumer : HumourConsumer
  longTermEquityConsumer : HumourConsumer

humourProject : HumourConsumer → HumourStudentState → Bool
humourProject threeCsConsumer _ = true
humourProject longTermEquityConsumer visibleLaughTrust = true
humourProject longTermEquityConsumer visibleLaughMasking = true
humourProject longTermEquityConsumer laterTrust = true
humourProject longTermEquityConsumer laterWithdrawal = false

humourProjectionFamily :
  Plural.ConsumerProjectionFamily
    HumourStudentState HumourAction HumourConsumer Bool
humourProjectionFamily =
  Plural.consumerProjectionFamily humourSystem humourProject

threeCsProjectionDynamicallySafe :
  Dynamic.DynamicConsumerSafety humourSystem (humourProject threeCsConsumer)
threeCsProjectionDynamicallySafe =
  Dynamic.dynamicConsumerSafety
    (λ sameCurrent leftExecution rightExecution → refl)

longTermEquityProjectionDefect :
  Dynamic.TerminalisationDefect
    humourSystem
    (humourProject longTermEquityConsumer)
longTermEquityProjectionDefect =
  Dynamic.terminalisationDefect
    (subsequentClassInteraction ∷ [])
    visibleLaughTrust
    visibleLaughMasking
    laterTrust
    laterWithdrawal
    refl
    trustExecution
    maskingExecution
    (λ ())

humourConsumerSafetyAsymmetry :
  Plural.ConsumerSafetyAsymmetry
    humourProjectionFamily
    threeCsConsumer
    longTermEquityConsumer
humourConsumerSafetyAsymmetry =
  Plural.consumerSafetyAsymmetry
    threeCsProjectionDynamicallySafe
    longTermEquityProjectionDefect

threeCsSafetyDoesNotEstablishPluralSafety :
  Plural.PluralDynamicSafety humourProjectionFamily → ⊥
threeCsSafetyDoesNotEstablishPluralSafety =
  Plural.asymmetryContradictsPluralSafety humourConsumerSafetyAsymmetry

------------------------------------------------------------------------
-- Aggregate-positive reception is not universal-positive reception.
------------------------------------------------------------------------

data SampleStudent : Set where
  studentOne studentTwo studentThree : SampleStudent

studentPositiveReception : SampleStudent → Bool
studentPositiveReception studentOne = true
studentPositiveReception studentTwo = true
studentPositiveReception studentThree = false

headlineAggregatePositive : Bool
headlineAggregatePositive = true

headlineAggregatePositiveIsTrue : headlineAggregatePositive ≡ true
headlineAggregatePositiveIsTrue = refl

universalPositiveReceptionImpossible :
  ((student : SampleStudent) → studentPositiveReception student ≡ true) →
  ⊥
universalPositiveReceptionImpossible allPositive with allPositive studentThree
... | ()

------------------------------------------------------------------------
-- Dialectical disagreement is an inhabited corridor, not framework failure.
------------------------------------------------------------------------

data HumourEvent : Set where
  canonicalHumourEvent : HumourEvent

humourDialecticField : Dialectic.DialecticField HumourEvent
humourDialecticField = Dialectic.dialecticField observeHumour
  where
    observeHumour :
      Dialectic.Stance → Dialectic.Predicate HumourEvent
    observeHumour Dialectic.thesisSide canonicalHumourEvent = true
    observeHumour Dialectic.antithesisSide canonicalHumourEvent = false

humourDisagreementCorridorIsLive :
  Dialectic.corridor humourDialecticField canonicalHumourEvent ≡ true
humourDisagreementCorridorIsLive = refl

------------------------------------------------------------------------
-- Canonical bridge.
------------------------------------------------------------------------

record HumourEpistemicAgencyHyperfabricBridge : Set₁ where
  constructor humourEpistemicAgencyHyperfabricBridge
  field
    sourceFramework : Humour.HumourFrameworkSourceSurface
    sourceFrameworkIsCanonical :
      sourceFramework ≡ Humour.canonicalHumourFrameworkSourceSurface

    laterVoiceAgencyBridge : Voice.StudentVoiceEpistemicAgencyBridge
    laterVoiceAgencyBridgeIsCanonical :
      laterVoiceAgencyBridge ≡ Voice.canonicalStudentVoiceEpistemicAgencyBridge

    situatedFeedbackHypervoxel : OEF.FeedbackHypervoxel
    situatedFeedbackHypervoxelIsCanonical :
      situatedFeedbackHypervoxel ≡ OEF.canonicalFeedbackHypervoxel

    governance :
      Governance.EpistemicGovernance Voice.EpistemicParticipationStage
    governanceIsCanonical : governance ≡ humourStageGovernance

    conditionalNormalizationCounterexample :
      Conditional.ConditionalNormalizationCounterexample
    conditionalNormalizationCounterexampleIsCanonical :
      conditionalNormalizationCounterexample
      ≡ Conditional.canonicalConditionalNormalizationCounterexample

    dynamicReceptionDefect :
      Dynamic.TerminalisationDefect
        humourSystem
        (humourProject longTermEquityConsumer)
    dynamicReceptionDefectIsCanonical :
      dynamicReceptionDefect ≡ longTermEquityProjectionDefect

    consumerSafetyAsymmetry :
      Plural.ConsumerSafetyAsymmetry
        humourProjectionFamily
        threeCsConsumer
        longTermEquityConsumer
    consumerSafetyAsymmetryIsCanonical :
      consumerSafetyAsymmetry ≡ humourConsumerSafetyAsymmetry

    feedbackDoesNotConferConstitutiveAuthority :
      (coordinate : Governance.InquiryCoordinate) →
      StageAuthorises Voice.feedbackSourceStage coordinate →
      ⊥

    flatAudienceCarrierMissesInstitutionalPower :
      (axis : FlatAudienceAxis) →
      embedFlatAudienceAxis axis ≡ institutionalPowerAxis →
      ⊥

    aggregatePositiveDoesNotMeanUniversalPositive :
      ((student : SampleStudent) → studentPositiveReception student ≡ true) →
      ⊥

    disagreementCorridorRetained :
      Dialectic.corridor humourDialecticField canonicalHumourEvent ≡ true

    reading : String

open HumourEpistemicAgencyHyperfabricBridge public

canonicalHumourEpistemicAgencyHyperfabricBridge :
  HumourEpistemicAgencyHyperfabricBridge
canonicalHumourEpistemicAgencyHyperfabricBridge =
  humourEpistemicAgencyHyperfabricBridge
    Humour.canonicalHumourFrameworkSourceSurface refl
    Voice.canonicalStudentVoiceEpistemicAgencyBridge refl
    OEF.canonicalFeedbackHypervoxel refl
    humourStageGovernance refl
    Conditional.canonicalConditionalNormalizationCounterexample refl
    longTermEquityProjectionDefect refl
    humourConsumerSafetyAsymmetry refl
    feedbackStageHasNoConstitutiveAuthority
    institutionalPowerHasNoFlatPreimage
    universalPositiveReceptionImpossible
    humourDisagreementCorridorIsLive
    "The earlier humour framework is preserved as a useful teacher-side projection, then governed by the later voice/agency distinction and the existing situated OEF hypervoxel. Feedback alone has no constitutive-governance constructor; flat audience descriptors embed strictly into a richer intersectional carrier; a 3Cs-visible positive surface can be dynamically safe for one consumer while a long-term equity consumer has an explicit quotient defect; respondent renormalisation is not cohort completeness; aggregate positive reception is not universal reception; and teacher/student disagreement remains an epistemically live dialectical corridor rather than noise."
