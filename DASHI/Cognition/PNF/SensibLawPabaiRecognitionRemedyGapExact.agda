module DASHI.Cognition.PNF.SensibLawPabaiRecognitionRemedyGapExact where

------------------------------------------------------------------------
-- PABAI: FACTUAL RECOGNITION / DOCTRINAL REMEDY GAP
--
-- Pabai v Commonwealth of Australia (No 2) [2025] FCA 796 is represented in
-- source layers. Factual findings, legal holdings, applicants' allegations,
-- later critical interpretation and appeal status are not interchangeable.
--
-- Appeal VID1479/2025 is recorded only as a procedural state: appeal filed and
-- oral submissions publicly recorded in July 2026. This file does not invent an
-- appeal disposition where no later appeal judgment has been entered here.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.DominantChartEpistemicCompressionExact as Compression

------------------------------------------------------------------------
-- Source / proposition layers.
------------------------------------------------------------------------

data PabaiLayer : Set where
  firstInstanceFactualFinding : PabaiLayer
  firstInstanceLegalHolding : PabaiLayer
  applicantAllegation : PabaiLayer
  criticalInterpretation : PabaiLayer
  appealProceduralStatus : PabaiLayer


record PabaiClaimReceipt : Set where
  constructor pabai-claim-receipt
  field
    claimId : String
    proposition : String
    layer : PabaiLayer
    sourceReference : String
    canonicalURL : String
    sourceSaysThisDirectly : Bool
    worldTruthBeyondAdjudicatedScope : Bool
    worldTruthBeyondAdjudicatedScopeIsFalse :
      worldTruthBeyondAdjudicatedScope ≡ false
    finalAppealDispositionClaimed : Bool
    finalAppealDispositionClaimedIsFalse :
      finalAppealDispositionClaimed ≡ false

open PabaiClaimReceipt public

severeClimateImpactFinding : PabaiClaimReceipt
severeClimateImpactFinding = pabai-claim-receipt
  "PABAI.1"
  "The first-instance court made factual findings of severe impacts of human-induced climate change on the Torres Strait Islands, including damage to ecosystems and traditional ways of life/Ailan Kastom"
  firstInstanceFactualFinding
  "Pabai v Commonwealth of Australia (No 2) [2025] FCA 796"
  "https://www.fedcourt.gov.au/services/access-to-files-and-transcripts/online-files/pabai-v-australia"
  true false refl false refl

bestAvailableScienceFinding : PabaiClaimReceipt
bestAvailableScienceFinding = pabai-claim-receipt
  "PABAI.2"
  "The first-instance court found that, for the 2015, 2020 and 2021 emissions targets, the Commonwealth failed to engage with or give genuine consideration to the best available science"
  firstInstanceFactualFinding
  "Pabai v Commonwealth of Australia (No 2) [2025] FCA 796"
  "https://www.fedcourt.gov.au/services/access-to-files-and-transcripts/online-files/pabai-v-australia"
  true false refl false refl

noDutyHolding : PabaiClaimReceipt
noDutyHolding = pabai-claim-receipt
  "PABAI.3"
  "The first-instance court held that the posited negligence duties were not established, materially because the relevant emissions-target and adaptation questions involved high or core government policy inappropriate for the asserted common-law duty"
  firstInstanceLegalHolding
  "Pabai v Commonwealth of Australia (No 2) [2025] FCA 796"
  "https://www.fedcourt.gov.au/services/access-to-files-and-transcripts/online-files/pabai-v-australia"
  true false refl false refl

ailanKastomCompensabilityHolding : PabaiClaimReceipt
ailanKastomCompensabilityHolding = pabai-claim-receipt
  "PABAI.4"
  "The first-instance court declined to extend negligence damages so that loss of fulfilment of Ailan Kastom constituted a compensable head of loss on the case as pleaded"
  firstInstanceLegalHolding
  "Pabai v Commonwealth of Australia (No 2) [2025] FCA 796"
  "https://www.fedcourt.gov.au/services/access-to-files-and-transcripts/online-files/pabai-v-australia"
  true false refl false refl

recognitionWithoutRemedyCriticalInterpretation : PabaiClaimReceipt
recognitionWithoutRemedyCriticalInterpretation = pabai-claim-receipt
  "PABAI.S1"
  "DASHI/SensibLaw critical interpretation: Pabai is an exact recognition/remedy-gap specimen because serious harm and important factual propositions can be judicially acknowledged while the selected negligence remedy remains unavailable"
  criticalInterpretation
  "DASHI/SensibLaw synthesis over [2025] FCA 796"
  "repo:DASHI/Cognition/PNF/SensibLawPabaiRecognitionRemedyGapExact.agda"
  false false refl false refl

appealFiledStatus : PabaiClaimReceipt
appealFiledStatus = pabai-claim-receipt
  "PABAI.A1"
  "Appeal VID1479/2025 was filed; the Federal Court online file records appellants' and respondent's written and oral-submission materials through 30 July 2026"
  appealProceduralStatus
  "Federal Court Online File, VID1479/2025"
  "https://www.fedcourt.gov.au/services/access-to-files-and-transcripts/online-files/pabai-v-australia"
  true false refl false refl

------------------------------------------------------------------------
-- Recognition does not mechanically factor to remedy.
--
-- The second state is explicitly synthetic. It is not a second Pabai fact. Its
-- sole role is to make the representation theorem exact: the same harm-
-- recognition surface is compatible with different remedy states, therefore
-- recognition alone is insufficient to determine remedy.
------------------------------------------------------------------------

data PabaiSituatedState : Set where
  actualFirstInstanceRecognitionRemedyUnavailable : PabaiSituatedState
  syntheticSameRecognitionRemedyAvailable : PabaiSituatedState


data HarmRecognitionSurface : Set where
  seriousClimateHarmRecognised : HarmRecognitionSurface

data NegligenceRemedyState : Set where
  negligenceRemedyUnavailable : NegligenceRemedyState
  negligenceRemedyAvailable : NegligenceRemedyState


harmRecognitionObserver : PabaiSituatedState → HarmRecognitionSurface
harmRecognitionObserver actualFirstInstanceRecognitionRemedyUnavailable = seriousClimateHarmRecognised
harmRecognitionObserver syntheticSameRecognitionRemedyAvailable = seriousClimateHarmRecognised

remedyState : PabaiSituatedState → NegligenceRemedyState
remedyState actualFirstInstanceRecognitionRemedyUnavailable = negligenceRemedyUnavailable
remedyState syntheticSameRecognitionRemedyAvailable = negligenceRemedyAvailable

remedyStatesDiffer :
  remedyState actualFirstInstanceRecognitionRemedyUnavailable ≡
  remedyState syntheticSameRecognitionRemedyAvailable → ⊥
remedyStatesDiffer ()

pabaiRecognitionRemedyNonfactorability :
  INF.NonFactorabilityWitness harmRecognitionObserver remedyState
pabaiRecognitionRemedyNonfactorability =
  INF.nonFactorabilityWitness
    actualFirstInstanceRecognitionRemedyUnavailable
    syntheticSameRecognitionRemedyAvailable
    refl
    remedyStatesDiffer

harmRecognitionCannotDetermineNegligenceRemedy :
  INF.FactorsThrough harmRecognitionObserver remedyState → ⊥
harmRecognitionCannotDetermineNegligenceRemedy =
  INF.witnessRulesOutEveryFlatFactorisation pabaiRecognitionRemedyNonfactorability

pabaiDominantChartReceipt :
  Compression.ProjectionInadequacyReceipt harmRecognitionObserver remedyState
pabaiDominantChartReceipt = Compression.projection-inadequacy-receipt
  Compression.juridicalRecognitionCompression
  "judicial factual-harm recognition surface"
  "consumer asking whether a negligence duty/remedy is legally available"
  "recognition of serious harm does not itself encode duty, compensability or remedy"
  pabaiRecognitionRemedyNonfactorability
  true refl
  false refl
  false refl
  false refl

------------------------------------------------------------------------
-- Procedural temporal state.
------------------------------------------------------------------------

data AppealState : Set where
  appealFiled : AppealState
  appealHeardMaterialsRecorded : AppealState
  appealJudgmentLocated : AppealState
  appealOutcomeUnresolvedInAtlas : AppealState


record PabaiAppealTemporalReceipt : Set where
  constructor pabai-appeal-temporal-receipt
  field
    appealReference : String
    publicFileAsOf : String
    noticeOfAppealRecorded : Bool
    noticeOfAppealRecordedIsTrue : noticeOfAppealRecorded ≡ true
    oralSubmissionMaterialsRecorded : Bool
    oralSubmissionMaterialsRecordedIsTrue : oralSubmissionMaterialsRecorded ≡ true
    appealJudgmentLocatedInCurrentAtlas : Bool
    appealJudgmentLocatedInCurrentAtlasIsFalse :
      appealJudgmentLocatedInCurrentAtlas ≡ false
    currentAtlasState : AppealState
    laterJudgmentMustSupersedeThisProceduralReceipt : Bool
    laterJudgmentMustSupersedeThisProceduralReceiptIsTrue :
      laterJudgmentMustSupersedeThisProceduralReceipt ≡ true

open PabaiAppealTemporalReceipt public

currentPabaiAppealReceipt : PabaiAppealTemporalReceipt
currentPabaiAppealReceipt = pabai-appeal-temporal-receipt
  "VID1479/2025"
  "Federal Court online file checked through materials published 30 July 2026; repository audit date 6 September 2026"
  true refl
  true refl
  false refl
  appealOutcomeUnresolvedInAtlas
  true refl

------------------------------------------------------------------------
-- Typed gap coordinates.
------------------------------------------------------------------------

data PabaiCoordinate : Set where
  physicalClimateHarm : PabaiCoordinate
  culturalAilanKastomHarm : PabaiCoordinate
  governmentScienceConsideration : PabaiCoordinate
  negligenceDuty : PabaiCoordinate
  compensableCulturalLoss : PabaiCoordinate
  damagesOrInjunctionRemedy : PabaiCoordinate
  appealOutcome : PabaiCoordinate


data PabaiCoordinateState : Set where
  factFound : PabaiCoordinateState
  legalRouteDenied : PabaiCoordinateState
  reliefNotObtainedAtFirstInstance : PabaiCoordinateState
  procedurallyLive : PabaiCoordinateState


coordinateState : PabaiCoordinate → PabaiCoordinateState
coordinateState physicalClimateHarm = factFound
coordinateState culturalAilanKastomHarm = factFound
coordinateState governmentScienceConsideration = factFound
coordinateState negligenceDuty = legalRouteDenied
coordinateState compensableCulturalLoss = legalRouteDenied
coordinateState damagesOrInjunctionRemedy = reliefNotObtainedAtFirstInstance
coordinateState appealOutcome = procedurallyLive

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data FactRecognitionImpliesNegligenceDuty : Set where
data FactRecognitionImpliesRemedy : Set where
data NoDutyHoldingMeansNoClimateHarm : Set where
data NoCompensableAilanKastomLossMeansNoAilanKastomHarm : Set where
data FirstInstanceHoldingEqualsAppealOutcome : Set where
data CriticalDoctrinalWallLanguageIsCourtHolding : Set where
data SyntheticCounterstateIsSecondPabaiFact : Set where

factRecognitionDoesNotCreateDuty : FactRecognitionImpliesNegligenceDuty → ⊥
factRecognitionDoesNotCreateDuty ()

factRecognitionDoesNotCreateRemedy : FactRecognitionImpliesRemedy → ⊥
factRecognitionDoesNotCreateRemedy ()

noDutyDoesNotEraseClimateHarmFinding : NoDutyHoldingMeansNoClimateHarm → ⊥
noDutyDoesNotEraseClimateHarmFinding ()

nonCompensabilityDoesNotEraseCulturalHarm :
  NoCompensableAilanKastomLossMeansNoAilanKastomHarm → ⊥
nonCompensabilityDoesNotEraseCulturalHarm ()

firstInstanceDoesNotPredetermineAppeal : FirstInstanceHoldingEqualsAppealOutcome → ⊥
firstInstanceDoesNotPredetermineAppeal ()

criticalLanguageDoesNotBecomeCourtAuthorship :
  CriticalDoctrinalWallLanguageIsCourtHolding → ⊥
criticalLanguageDoesNotBecomeCourtAuthorship ()

syntheticCounterstateDoesNotBecomeCaseFact : SyntheticCounterstateIsSecondPabaiFact → ⊥
syntheticCounterstateDoesNotBecomeCaseFact ()

record PabaiRecognitionRemedyBoundary : Set where
  constructor pabai-recognition-remedy-boundary
  field
    seriousClimateHarmRecognisedAtFirstInstance : Bool
    seriousClimateHarmRecognisedAtFirstInstanceIsTrue :
      seriousClimateHarmRecognisedAtFirstInstance ≡ true
    assertedNegligenceDutyEstablished : Bool
    assertedNegligenceDutyEstablishedIsFalse : assertedNegligenceDutyEstablished ≡ false
    AilanKastomLossAcceptedAsCompensableNegligenceHead : Bool
    AilanKastomLossAcceptedAsCompensableNegligenceHeadIsFalse :
      AilanKastomLossAcceptedAsCompensableNegligenceHead ≡ false
    recognitionAutomaticallyProducesRemedy : Bool
    recognitionAutomaticallyProducesRemedyIsFalse :
      recognitionAutomaticallyProducesRemedy ≡ false
    appealProcedurallyLiveInCurrentAtlas : Bool
    appealProcedurallyLiveInCurrentAtlasIsTrue : appealProcedurallyLiveInCurrentAtlas ≡ true
    firstInstanceResultTreatedAsFinalAppealLaw : Bool
    firstInstanceResultTreatedAsFinalAppealLawIsFalse :
      firstInstanceResultTreatedAsFinalAppealLaw ≡ false
    syntheticCounterstatePromotedToCaseFact : Bool
    syntheticCounterstatePromotedToCaseFactIsFalse :
      syntheticCounterstatePromotedToCaseFact ≡ false

open PabaiRecognitionRemedyBoundary public

canonicalPabaiRecognitionRemedyBoundary : PabaiRecognitionRemedyBoundary
canonicalPabaiRecognitionRemedyBoundary = pabai-recognition-remedy-boundary
  true refl false refl false refl false refl true refl false refl false refl
