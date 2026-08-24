module DASHI.Biology.AliceBrownCorpusLoom where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Biology.EducationCorpusSourceRegistry as Sources
import DASHI.Biology.OEFAIFeedbackFormalisationFull as AI
import DASHI.Biology.HumourOnlineEngagementFramework as Humour
import DASHI.Biology.HumourEpistemicAgencyHyperfabricBridge as HumourAgency
import DASHI.Biology.StudentVoiceEpistemicAgencyBridge as Voice
import DASHI.Biology.StudentIdentifiedSupportStrategiesBridge as Strategies
import DASHI.Biology.EcologyOfDataHyperfabricBridge as Ecology
import DASHI.Biology.ParentAllyshipMultiObserverBridge as Allyship
import DASHI.Biology.ParentalFearIndependentMobilityExact as FearMobility
import DASHI.Biology.ParentalFearSourceAttributionExact as FearAttribution
import DASHI.Biology.ParentalFearObserverRefinementExact as FearObserver
import DASHI.Biology.InterpretiveCodingSystem as Coding
import DASHI.Biology.CrossPaperDialecticalDevelopment as Development

------------------------------------------------------------------------
-- Corpus-level loom.
--
-- This aggregate preserves each source paper as its own fibre, while exposing
-- typed cross-paper relations and DASHI extensions.  It does not flatten the
-- corpus into one claimed theory or promote any author/paper to authority.
--
-- The humour/agency bridge lives in Set1 because its governance and plural
-- dynamic-safety fields themselves quantify over typed relations.
------------------------------------------------------------------------

record AliceBrownCorpusLoom : Set₁ where
  constructor mkAliceBrownCorpusLoom
  field
    sourceRegistry : Sources.EducationCorpusSourceRegistry
    sourceRegistryIsCanonical :
      sourceRegistry ≡ Sources.canonicalEducationCorpusSourceRegistry

    aiFeedbackFormalisation : AI.OEFAIFeedbackFormalisationFull
    aiFeedbackFormalisationIsCanonical :
      aiFeedbackFormalisation ≡ AI.canonicalOEFAIFeedbackFormalisationFull

    humourFramework : Humour.HumourFrameworkSourceSurface
    humourFrameworkIsCanonical :
      humourFramework ≡ Humour.canonicalHumourFrameworkSourceSurface

    humourEpistemicAgencyBridge :
      HumourAgency.HumourEpistemicAgencyHyperfabricBridge
    humourEpistemicAgencyBridgeIsCanonical :
      humourEpistemicAgencyBridge
      ≡ HumourAgency.canonicalHumourEpistemicAgencyHyperfabricBridge

    studentVoiceAgencyBridge : Voice.StudentVoiceEpistemicAgencyBridge
    studentVoiceAgencyBridgeIsCanonical :
      studentVoiceAgencyBridge ≡ Voice.canonicalStudentVoiceEpistemicAgencyBridge

    supportStrategiesBridge : Strategies.StudentIdentifiedSupportStrategiesBridge
    supportStrategiesBridgeIsCanonical :
      supportStrategiesBridge ≡
      Strategies.canonicalStudentIdentifiedSupportStrategiesBridge

    ecologyHyperfabricBridge : Ecology.EcologyOfDataHyperfabricBridge
    ecologyHyperfabricBridgeIsCanonical :
      ecologyHyperfabricBridge ≡ Ecology.canonicalEcologyOfDataHyperfabricBridge

    parentAllyshipBridge : Allyship.ParentAllyshipMultiObserverBridge
    parentAllyshipBridgeIsCanonical :
      parentAllyshipBridge ≡ Allyship.canonicalParentAllyshipMultiObserverBridge

    parentalFearMobilityBridge : FearMobility.ParentalFearEcologyBridge
    parentalFearMobilityBridgeIsCanonical :
      parentalFearMobilityBridge ≡ FearMobility.canonicalParentalFearEcologyBridge

    parentalFearAttribution : FearAttribution.ParentalFearSourceAttribution
    parentalFearAttributionIsCanonical :
      parentalFearAttribution ≡
      FearAttribution.canonicalParentalFearSourceAttribution

    parentalFearObserverRefinement :
      FearObserver.ParentalFearObserverRefinementBridge
    parentalFearObserverRefinementIsCanonical :
      parentalFearObserverRefinement ≡
      FearObserver.canonicalParentalFearObserverRefinementBridge

    interpretiveCodingSystem : Coding.InterpretiveCodingSystem
    interpretiveCodingSystemIsCanonical :
      interpretiveCodingSystem ≡ Coding.canonicalInterpretiveCodingSystem

    dialecticalDevelopment : Development.CrossPaperDialecticalDevelopment
    dialecticalDevelopmentIsCanonical :
      dialecticalDevelopment ≡
      Development.canonicalCrossPaperDialecticalDevelopment

    paperFibresNotFlattened : Bool
    paperFibresNotFlattenedIsTrue : paperFibresNotFlattened ≡ true

    sourceClaimsNotCrossPaperInferences : Bool
    sourceClaimsNotCrossPaperInferencesIsTrue :
      sourceClaimsNotCrossPaperInferences ≡ true

    crossPaperInferencesNotEmpiricalResults : Bool
    crossPaperInferencesNotEmpiricalResultsIsTrue :
      crossPaperInferencesNotEmpiricalResults ≡ true

    studentAndParentObserverFibresRemainDistinct : Bool
    studentAndParentObserverFibresRemainDistinctIsTrue :
      studentAndParentObserverFibresRemainDistinct ≡ true

    agencyAndCustodianshipGovernDownstreamUse : Bool
    agencyAndCustodianshipGovernDownstreamUseIsTrue :
      agencyAndCustodianshipGovernDownstreamUse ≡ true

    humourSourcePreservedBeforeDialecticalCorrection : Bool
    humourSourcePreservedBeforeDialecticalCorrectionIsTrue :
      humourSourcePreservedBeforeDialecticalCorrection ≡ true

    parentalFearSourcePreservedBeforeEcologyBridge : Bool
    parentalFearSourcePreservedBeforeEcologyBridgeIsTrue :
      parentalFearSourcePreservedBeforeEcologyBridge ≡ true

    parentalFearAttributionRetainedThroughExtensions : Bool
    parentalFearAttributionRetainedThroughExtensionsIsTrue :
      parentalFearAttributionRetainedThroughExtensions ≡ true

    corpusLoomCandidateOnly : Bool
    corpusLoomCandidateOnlyIsTrue : corpusLoomCandidateOnly ≡ true

    reading : String

open AliceBrownCorpusLoom public

canonicalAliceBrownCorpusLoom : AliceBrownCorpusLoom
canonicalAliceBrownCorpusLoom =
  mkAliceBrownCorpusLoom
    Sources.canonicalEducationCorpusSourceRegistry refl
    AI.canonicalOEFAIFeedbackFormalisationFull refl
    Humour.canonicalHumourFrameworkSourceSurface refl
    HumourAgency.canonicalHumourEpistemicAgencyHyperfabricBridge refl
    Voice.canonicalStudentVoiceEpistemicAgencyBridge refl
    Strategies.canonicalStudentIdentifiedSupportStrategiesBridge refl
    Ecology.canonicalEcologyOfDataHyperfabricBridge refl
    Allyship.canonicalParentAllyshipMultiObserverBridge refl
    FearMobility.canonicalParentalFearEcologyBridge refl
    FearAttribution.canonicalParentalFearSourceAttribution refl
    FearObserver.canonicalParentalFearObserverRefinementBridge refl
    Coding.canonicalInterpretiveCodingSystem refl
    Development.canonicalCrossPaperDialecticalDevelopment refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    "Corpus-level candidate loom: the OEF/AI paper supplies scalable proxy classification; the source-bound humour paper supplies a seven-consideration teacher-side pedagogical framework; the humour/agency hyperfabric bridge exposes constitutive governance, strict intersectional carrier expansion, conditional-normalisation and plural-dynamic-safety boundaries without rewriting the source; voice/agency supplies epistemic-participation gates; online-support research supplies student-identified +1 families; ecology-of-data supplies person-place custodianship; dyslexia allyship research supplies plural observer and proximity fibres; the parental fear/IAST study supplies a situated reciprocal negotiation model with opposed place readings, plural stranger meanings, benefit/fear tension and parent-action feedback; its O'Connor/Brown 2013 Health & Place attribution and DOI remain first-class through downstream extensions; the observer-refinement bridge proves that coarse fear alone need not determine an intervention-relevant contextual distinction; and the interpretive-coding interface exposes the common human/machine mediation layer. Source claims, cross-paper inferences, DASHI extensions and future empirical tests remain distinct."

canonicalCorpusLoomSourceCountReading : String
canonicalCorpusLoomSourceCountReading =
  "nine source-bound papers/items with title, authors, DOI-or-explicit-no-DOI, venue and boundary metadata"