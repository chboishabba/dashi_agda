module DASHI.Biology.ParentalFearIndependentMobilityExact where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Biology.EducationCorpusSourceRegistry as Sources
import DASHI.Biology.EcologyOfDataHyperfabricBridge as Ecology

------------------------------------------------------------------------
-- Source-bound formalisation of:
--
-- O'Connor, Justen; Brown, Alice (2013).
-- "A qualitative study of 'fear' as a regulator of children's independent
-- physical activity in the suburbs." Health & Place 24, 157-164.
-- DOI: 10.1016/j.healthplace.2013.09.002.
--
-- The source studies parental negotiations of fear and risk around
-- independent active school travel (IAST) in one white middle-class
-- Australian suburban setting.  It uses Tudor's parameters-of-fear frame,
-- but the analysis explicitly moves away from rigid, unidirectional fitting:
-- the parameters are interwoven, mutually modifying and context-sensitive.
--
-- This module therefore formalises the paper as a situated multi-fibre
-- decision system, not as a universal causal model, a prevalence estimate,
-- or a claim that fear can be reduced to one scalar or rational/irrational
-- binary.
------------------------------------------------------------------------

listCount : ∀ {A : Set} → List A → Nat
listCount [] = zero
listCount (_ ∷ xs) = suc (listCount xs)

------------------------------------------------------------------------
-- Tudor parameter fibres used by the study.

data FearParameter : Set where
  environment : FearParameter
  culture : FearParameter
  socialStructure : FearParameter
  body : FearParameter
  personality : FearParameter
  socialSubject : FearParameter

canonicalFearParameters : List FearParameter
canonicalFearParameters =
  environment
  ∷ culture
  ∷ socialStructure
  ∷ body
  ∷ personality
  ∷ socialSubject
  ∷ []

canonicalFearParameterCount : listCount canonicalFearParameters ≡ 6
canonicalFearParameterCount = refl

parameterName : FearParameter → String
parameterName environment = "environment"
parameterName culture = "culture"
parameterName socialStructure = "social structure"
parameterName body = "body"
parameterName personality = "personality"
parameterName socialSubject = "social subject"

record SituatedFearHypervoxel : Set where
  constructor mkSituatedFearHypervoxel
  field
    placeSurface : String
    culturalSurface : String
    socialStructureSurface : String
    bodySurface : String
    personalitySurface : String
    socialSubjectSurface : String
    temporalSurface : String
    childCapabilitySurface : String
    mobilitySurface : String
    fearSurface : String
    benefitSurface : String

open SituatedFearHypervoxel public

canonicalSituatedFearHypervoxel : SituatedFearHypervoxel
canonicalSituatedFearHypervoxel =
  mkSituatedFearHypervoxel
    "leafy outer bayside suburban place, routes, traffic, sightlines and footpaths"
    "media, local alerts, parenting norms and competing health / independence discourses"
    "family, school, neighbours, recognisable strangers, siblings, routines and community connectivity"
    "parent bodily fear response and perceived child bodily capability"
    "parent self-described calm / protective / conservative dispositions and control preferences"
    "first- and second-hand encounters, biographies and close-network experiences"
    "changing readiness, age, experience and repeated renegotiation"
    "traffic judgement, bike handling, strength, independence and learned safety strategies"
    "independent active school travel and adult accompaniment choices"
    "situated fearfulness including traffic, stranger danger and fear of not knowing"
    "health, resilience, fitness, independence, life skills, play and environmental awareness"

------------------------------------------------------------------------
-- The same local feature can support opposed situated readings.
-- This is the concrete anti-reduction witness behind the paper's account of
-- attractive natural features that also create hiding places / poor sightlines.

data PlaceValence : Set where
  securitySupporting : PlaceValence
  fearSupporting : PlaceValence

record PlaceReading : Set where
  constructor mkPlaceReading
  field
    placeFeature : String
    placeValence : PlaceValence
    interpretation : String

open PlaceReading public

naturalSettingSecurityReading : PlaceReading
naturalSettingSecurityReading =
  mkPlaceReading
    "leafy natural streetscape"
    securitySupporting
    "beautiful / village-like setting supporting an embodied sense of security"

naturalSettingFearReading : PlaceReading
naturalSettingFearReading =
  mkPlaceReading
    "leafy natural streetscape"
    fearSupporting
    "scrub, limited sightlines and absent footpaths can increase anxiety about hidden people and traffic"

samePlaceFeatureOpposedReading :
  placeFeature naturalSettingSecurityReading
  ≡ placeFeature naturalSettingFearReading
samePlaceFeatureOpposedReading = refl

------------------------------------------------------------------------
-- 'Stranger' is not a stable binary category in the interviews.

data StrangerInterpretation : Set where
  threateningStranger : StrangerInterpretation
  neutralUnknownPerson : StrangerInterpretation
  potentialGuardian : StrangerInterpretation

canonicalStrangerInterpretations : List StrangerInterpretation
canonicalStrangerInterpretations =
  threateningStranger
  ∷ neutralUnknownPerson
  ∷ potentialGuardian
  ∷ []

canonicalStrangerInterpretationCount :
  listCount canonicalStrangerInterpretations ≡ 3
canonicalStrangerInterpretationCount = refl

record StrangerMeaningBoundary : Set where
  constructor mkStrangerMeaningBoundary
  field
    multipleSituatedMeanings : Bool
    multipleSituatedMeaningsIsTrue : multipleSituatedMeanings ≡ true
    notReducibleToUnknownEqualsThreat : Bool
    notReducibleToUnknownEqualsThreatIsTrue :
      notReducibleToUnknownEqualsThreat ≡ true
    knownPeopleCanAlsoBeRiskSources : Bool
    knownPeopleCanAlsoBeRiskSourcesIsTrue :
      knownPeopleCanAlsoBeRiskSources ≡ true

open StrangerMeaningBoundary public

canonicalStrangerMeaningBoundary : StrangerMeaningBoundary
canonicalStrangerMeaningBoundary =
  mkStrangerMeaningBoundary true refl true refl true refl

------------------------------------------------------------------------
-- Parent decision tension: acknowledged benefits coexist with the 'what if?'
-- question; awareness of low probability does not erase embodied fear.

data IASTBenefit : Set where
  resilience : IASTBenefit
  fitness : IASTBenefit
  independence : IASTBenefit
  improvedFunctioning : IASTBenefit
  unstructuredPlay : IASTBenefit
  environmentalAwareness : IASTBenefit
  lifeSkills : IASTBenefit

canonicalIASTBenefits : List IASTBenefit
canonicalIASTBenefits =
  resilience
  ∷ fitness
  ∷ independence
  ∷ improvedFunctioning
  ∷ unstructuredPlay
  ∷ environmentalAwareness
  ∷ lifeSkills
  ∷ []

canonicalIASTBenefitCount : listCount canonicalIASTBenefits ≡ 7
canonicalIASTBenefitCount = refl

record ProbabilityFearTension : Set where
  constructor mkProbabilityFearTension
  field
    smallProbabilityCanBeArticulated : Bool
    smallProbabilityCanBeArticulatedIsTrue :
      smallProbabilityCanBeArticulated ≡ true
    bodilyFearCanRemainPowerful : Bool
    bodilyFearCanRemainPowerfulIsTrue : bodilyFearCanRemainPowerful ≡ true
    benefitAwarenessCanCoexistWithFear : Bool
    benefitAwarenessCanCoexistWithFearIsTrue :
      benefitAwarenessCanCoexistWithFear ≡ true
    rationalIrrationalBinaryRejected : Bool
    rationalIrrationalBinaryRejectedIsTrue :
      rationalIrrationalBinaryRejected ≡ true

open ProbabilityFearTension public

canonicalProbabilityFearTension : ProbabilityFearTension
canonicalProbabilityFearTension =
  mkProbabilityFearTension true refl true refl true refl true refl

------------------------------------------------------------------------
-- Strategies parents report using to mediate fear and expand IAST.

data FearMediationStrategy : Set where
  developChildSkills : FearMediationStrategy
  waitForCapabilities : FearMediationStrategy
  buildTrustThroughGuidanceOrSurveillance : FearMediationStrategy
  establishCommunicationSystems : FearMediationStrategy
  broadenSocialNetwork : FearMediationStrategy

canonicalFearMediationStrategies : List FearMediationStrategy
canonicalFearMediationStrategies =
  developChildSkills
  ∷ waitForCapabilities
  ∷ buildTrustThroughGuidanceOrSurveillance
  ∷ establishCommunicationSystems
  ∷ broadenSocialNetwork
  ∷ []

canonicalFearMediationStrategyCount :
  listCount canonicalFearMediationStrategies ≡ 5
canonicalFearMediationStrategyCount = refl

------------------------------------------------------------------------
-- Dynamic / feedback reading of the study.
--
-- The paper's discussion says the negotiations and actions of parents do not
-- merely receive macro and micro influences; they also act back on those
-- drivers and subsequent behaviour.  Static agency/structure boundaries are
-- therefore deliberately rejected here.

record FearNegotiationDynamics : Set where
  constructor mkFearNegotiationDynamics
  field
    parametersAnalyticallyDistinguishable : Bool
    parametersAnalyticallyDistinguishableIsTrue :
      parametersAnalyticallyDistinguishable ≡ true
    parametersMutuallyModify : Bool
    parametersMutuallyModifyIsTrue : parametersMutuallyModify ≡ true
    parentalActionFeedsBackIntoContext : Bool
    parentalActionFeedsBackIntoContextIsTrue :
      parentalActionFeedsBackIntoContext ≡ true
    fearRepeatedlyRenegotiated : Bool
    fearRepeatedlyRenegotiatedIsTrue : fearRepeatedlyRenegotiated ≡ true
    staticAgencyStructureBoundaryRejected : Bool
    staticAgencyStructureBoundaryRejectedIsTrue :
      staticAgencyStructureBoundaryRejected ≡ true
    singularGlobalFearNarrativeRejected : Bool
    singularGlobalFearNarrativeRejectedIsTrue :
      singularGlobalFearNarrativeRejected ≡ true

open FearNegotiationDynamics public

canonicalFearNegotiationDynamics : FearNegotiationDynamics
canonicalFearNegotiationDynamics =
  mkFearNegotiationDynamics
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl

------------------------------------------------------------------------
-- Source-level formalisation with explicit empirical boundary.

record ParentalFearIndependentMobilitySource : Set where
  constructor mkParentalFearIndependentMobilitySource
  field
    sourcePaper : Sources.PaperReference
    sourcePaperIsCanonical :
      sourcePaper ≡ Sources.parentalFearIndependentMobilityPaper
    parameters : List FearParameter
    parametersAreCanonical : parameters ≡ canonicalFearParameters
    situatedState : SituatedFearHypervoxel
    situatedStateIsCanonical :
      situatedState ≡ canonicalSituatedFearHypervoxel
    strangerBoundary : StrangerMeaningBoundary
    strangerBoundaryIsCanonical :
      strangerBoundary ≡ canonicalStrangerMeaningBoundary
    probabilityFearTension : ProbabilityFearTension
    probabilityFearTensionIsCanonical :
      probabilityFearTension ≡ canonicalProbabilityFearTension
    mediationStrategies : List FearMediationStrategy
    mediationStrategiesAreCanonical :
      mediationStrategies ≡ canonicalFearMediationStrategies
    dynamics : FearNegotiationDynamics
    dynamicsAreCanonical : dynamics ≡ canonicalFearNegotiationDynamics
    qualitativeSituatedStudy : Bool
    qualitativeSituatedStudyIsTrue : qualitativeSituatedStudy ≡ true
    noPopulationPrevalenceClaim : Bool
    noPopulationPrevalenceClaimIsTrue : noPopulationPrevalenceClaim ≡ true
    noUniversalParentTrajectoryClaim : Bool
    noUniversalParentTrajectoryClaimIsTrue :
      noUniversalParentTrajectoryClaim ≡ true
    childVoiceAbsentFromSample : Bool
    childVoiceAbsentFromSampleIsTrue : childVoiceAbsentFromSample ≡ true
    reading : String

open ParentalFearIndependentMobilitySource public

canonicalParentalFearIndependentMobilitySource :
  ParentalFearIndependentMobilitySource
canonicalParentalFearIndependentMobilitySource =
  mkParentalFearIndependentMobilitySource
    Sources.parentalFearIndependentMobilityPaper refl
    canonicalFearParameters refl
    canonicalSituatedFearHypervoxel refl
    canonicalStrangerMeaningBoundary refl
    canonicalProbabilityFearTension refl
    canonicalFearMediationStrategies refl
    canonicalFearNegotiationDynamics refl
    true refl
    true refl
    true refl
    true refl
    "Source-bound reading: parental regulation of independent active school travel is produced through repeated negotiation among six interwoven Tudor parameter fibres. Place, strangers, probability, bodily fear, child capability, perceived benefits and available mediation strategies do not collapse to a single fear score or rational/irrational binary. The evidence is situated qualitative parent testimony, not a universal causal law or prevalence estimate."

------------------------------------------------------------------------
-- In-repository bridge.
--
-- This section is a DASHI extension, not a claim made in the 2013 paper.
-- It places the source formalisation beside the repository's existing
-- ecology-of-data hyperfabric.  The shared structural commitment is that a
-- local observation / decision surface is not the whole situated ecology.

record ParentalFearEcologyBridge : Set where
  constructor mkParentalFearEcologyBridge
  field
    sourceFormalisation : ParentalFearIndependentMobilitySource
    sourceFormalisationIsCanonical :
      sourceFormalisation ≡ canonicalParentalFearIndependentMobilitySource
    repoEcologyBridge : Ecology.EcologyOfDataHyperfabricBridge
    repoEcologyBridgeIsCanonical :
      repoEcologyBridge ≡ Ecology.canonicalEcologyOfDataHyperfabricBridge
    personPlaceContextRetained : Bool
    personPlaceContextRetainedIsTrue : personPlaceContextRetained ≡ true
    localFearLabelNotWholeEcology : Bool
    localFearLabelNotWholeEcologyIsTrue :
      localFearLabelNotWholeEcology ≡ true
    opposedLocalReadingsPreserved : Bool
    opposedLocalReadingsPreservedIsTrue :
      opposedLocalReadingsPreserved ≡ true
    feedbackNotFlattenedToLinearDriverChain : Bool
    feedbackNotFlattenedToLinearDriverChainIsTrue :
      feedbackNotFlattenedToLinearDriverChain ≡ true
    sourceClaimSeparatedFromDashiExtension : Bool
    sourceClaimSeparatedFromDashiExtensionIsTrue :
      sourceClaimSeparatedFromDashiExtension ≡ true
    reading : String

open ParentalFearEcologyBridge public

canonicalParentalFearEcologyBridge : ParentalFearEcologyBridge
canonicalParentalFearEcologyBridge =
  mkParentalFearEcologyBridge
    canonicalParentalFearIndependentMobilitySource refl
    Ecology.canonicalEcologyOfDataHyperfabricBridge refl
    true refl
    true refl
    true refl
    true refl
    true refl
    "DASHI extension: the 2013 fear/IAST study inhabits the repository's person-place, multi-fibre style without being rewritten as the later ecology-of-data theory. The bridge preserves contextual fibres, conflicting local readings and reciprocal feedback while keeping source claims and cross-paper formal synthesis distinct."
