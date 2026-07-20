module DASHI.Promotion.TechSystemicStressScenarioBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Foundations.SSPTritCarrier as Trit
import DASHI.Promotion.PNFSpectralTradingSignalBoundary as Trading
import DASHI.Promotion.PNFSpectralEmpiricalBasinValidation as Basin

------------------------------------------------------------------------
-- Tech/systemic stress scenario boundary.
--
-- This module records the typed architecture discussed for market-driven
-- cellular-automaton and news-alignment experiments.  It separates:
--
--   observation -> structural classification -> capital posture -> execution
--
-- and keeps all empirical and financial claims fail-closed.  In particular,
-- an adverse structural state is not definitionally a negative return, a
-- short signal, a news prediction, or a sovereign-crisis prediction.
--
-- The signed carrier reuses the canonical SSP trit {-1,0,+1}.  The three
-- values mean adverse / unresolved / favorable structural condition at the
-- classification layer.  They do not identify price direction.

------------------------------------------------------------------------
-- Signed structural regime and posture carriers.

data StructuralRegimeMeaning : Set where
  adverseStructuralRegime : StructuralRegimeMeaning
  unresolvedStructuralRegime : StructuralRegimeMeaning
  favorableStructuralRegime : StructuralRegimeMeaning

regimeMeaning : Trit.SSPTrit → StructuralRegimeMeaning
regimeMeaning Trit.sspNegOne = adverseStructuralRegime
regimeMeaning Trit.sspZero = unresolvedStructuralRegime
regimeMeaning Trit.sspPosOne = favorableStructuralRegime

data CapitalPosture : Set where
  defensivePosture : CapitalPosture
  observationalPosture : CapitalPosture
  opportunityPosture : CapitalPosture

postureFromRegime : Trit.SSPTrit → CapitalPosture
postureFromRegime Trit.sspNegOne = defensivePosture
postureFromRegime Trit.sspZero = observationalPosture
postureFromRegime Trit.sspPosOne = opportunityPosture

data ExecutionFamily : Set where
  flatExecution : ExecutionFamily
  carryOnlyExecution : ExecutionFamily
  boundedHedgeExecution : ExecutionFamily
  directionalExecution : ExecutionFamily
  convexityCandidateExecution : ExecutionFamily
  unavailableExecution : ExecutionFamily

record PostureExecutionBoundary : Set where
  field
    posture : CapitalPosture
    permittedExecutionFamilies : List ExecutionFamily
    futureReturnUsed : Bool
    futureReturnUsedIsFalse : futureReturnUsed ≡ false
    arbitrarySignInversionAllowed : Bool
    arbitrarySignInversionAllowedIsFalse :
      arbitrarySignInversionAllowed ≡ false
    productionTradingAuthority : Bool
    productionTradingAuthorityIsFalse :
      productionTradingAuthority ≡ false

open PostureExecutionBoundary public

canonicalDefensiveBoundary : PostureExecutionBoundary
canonicalDefensiveBoundary =
  record
    { posture = defensivePosture
    ; permittedExecutionFamilies =
        flatExecution
        ∷ carryOnlyExecution
        ∷ boundedHedgeExecution
        ∷ convexityCandidateExecution
        ∷ []
    ; futureReturnUsed = false
    ; futureReturnUsedIsFalse = refl
    ; arbitrarySignInversionAllowed = false
    ; arbitrarySignInversionAllowedIsFalse = refl
    ; productionTradingAuthority = false
    ; productionTradingAuthorityIsFalse = refl
    }

canonicalObservationalBoundary : PostureExecutionBoundary
canonicalObservationalBoundary =
  record
    { posture = observationalPosture
    ; permittedExecutionFamilies =
        flatExecution ∷ carryOnlyExecution ∷ []
    ; futureReturnUsed = false
    ; futureReturnUsedIsFalse = refl
    ; arbitrarySignInversionAllowed = false
    ; arbitrarySignInversionAllowedIsFalse = refl
    ; productionTradingAuthority = false
    ; productionTradingAuthorityIsFalse = refl
    }

canonicalOpportunityBoundary : PostureExecutionBoundary
canonicalOpportunityBoundary =
  record
    { posture = opportunityPosture
    ; permittedExecutionFamilies =
        directionalExecution
        ∷ boundedHedgeExecution
        ∷ carryOnlyExecution
        ∷ []
    ; futureReturnUsed = false
    ; futureReturnUsedIsFalse = refl
    ; arbitrarySignInversionAllowed = false
    ; arbitrarySignInversionAllowedIsFalse = refl
    ; productionTradingAuthority = false
    ; productionTradingAuthorityIsFalse = refl
    }

------------------------------------------------------------------------
-- Observable stress axes.

data StressAxis : Set where
  liquidityStressAxis : StressAxis
  fundingStressAxis : StressAxis
  correlationStressAxis : StressAxis
  narrativeInstabilityAxis : StressAxis
  executionChurnAxis : StressAxis
  treasuryFunctioningAxis : StressAxis
  creditTransmissionAxis : StressAxis
  technologyConcentrationAxis : StressAxis
  capexRevisionAxis : StressAxis
  secondaryHardwareMarketAxis : StressAxis
  powerAndCoolingConstraintAxis : StressAxis

canonicalStressAxes : List StressAxis
canonicalStressAxes =
  liquidityStressAxis
  ∷ fundingStressAxis
  ∷ correlationStressAxis
  ∷ narrativeInstabilityAxis
  ∷ executionChurnAxis
  ∷ treasuryFunctioningAxis
  ∷ creditTransmissionAxis
  ∷ technologyConcentrationAxis
  ∷ capexRevisionAxis
  ∷ secondaryHardwareMarketAxis
  ∷ powerAndCoolingConstraintAxis
  ∷ []

data StressObservationKind : Set where
  observedMarketDatum : StressObservationKind
  derivedProxyDatum : StressObservationKind
  caStructuralStatistic : StressObservationKind
  newsAlignedEventDatum : StressObservationKind
  unavailableObservation : StressObservationKind

record StressAxisObservation : Set where
  field
    observationId : String
    axis : StressAxis
    observationKind : StressObservationKind
    sourceSurface : Trading.MarketInformationSurface
    timeWindow : String
    valueDigest : String
    sourceReceiptId : String
    sourceReceiptSupplied : Bool
    sourceReceiptSuppliedIsFalseByDefault :
      sourceReceiptSupplied ≡ false
    causalInterpretationClaimed : Bool
    causalInterpretationClaimedIsFalse :
      causalInterpretationClaimed ≡ false
    predictionClaimed : Bool
    predictionClaimedIsFalse : predictionClaimed ≡ false

open StressAxisObservation public

canonicalStressObservation : StressAxisObservation
canonicalStressObservation =
  record
    { observationId = "canonical unvalidated stress-axis observation"
    ; axis = correlationStressAxis
    ; observationKind = caStructuralStatistic
    ; sourceSurface = Trading.receiptBackedReplaySurface
    ; timeWindow = "event-aligned replay window pending receipt"
    ; valueDigest = "multi-scale change/tension digest pending replay"
    ; sourceReceiptId = "missing stress observation receipt"
    ; sourceReceiptSupplied = false
    ; sourceReceiptSuppliedIsFalseByDefault = refl
    ; causalInterpretationClaimed = false
    ; causalInterpretationClaimedIsFalse = refl
    ; predictionClaimed = false
    ; predictionClaimedIsFalse = refl
    }

------------------------------------------------------------------------
-- Crisis phase ladder: warning, proximity, active dysfunction, stabilization.

data StressPhase : Set where
  latentFragilityPhase : StressPhase
  triggerProximityPhase : StressPhase
  activeDysfunctionPhase : StressPhase
  stabilizationPhase : StressPhase
  unresolvedPhase : StressPhase

record StressPhaseAssessment : Set where
  field
    assessmentId : String
    phase : StressPhase
    signedRegime : Trit.SSPTrit
    observations : List StressAxisObservation
    linkedBasinRegion : Basin.BasinRegion
    phaseDigest : String
    replayReceiptId : String
    replayReceiptSupplied : Bool
    replayReceiptSuppliedIsFalseByDefault :
      replayReceiptSupplied ≡ false
    deterministicCountdownClaim : Bool
    deterministicCountdownClaimIsFalse :
      deterministicCountdownClaim ≡ false
    sovereignCrisisClaim : Bool
    sovereignCrisisClaimIsFalse : sovereignCrisisClaim ≡ false

open StressPhaseAssessment public

canonicalLatentFragilityAssessment : StressPhaseAssessment
canonicalLatentFragilityAssessment =
  record
    { assessmentId = "canonical latent-fragility candidate"
    ; phase = latentFragilityPhase
    ; signedRegime = Trit.sspZero
    ; observations = canonicalStressObservation ∷ []
    ; linkedBasinRegion = Basin.unresolvedBasinRegion
    ; phaseDigest = "latent fragility requires rising cross-axis receipts"
    ; replayReceiptId = "missing latent-fragility replay receipt"
    ; replayReceiptSupplied = false
    ; replayReceiptSuppliedIsFalseByDefault = refl
    ; deterministicCountdownClaim = false
    ; deterministicCountdownClaimIsFalse = refl
    ; sovereignCrisisClaim = false
    ; sovereignCrisisClaimIsFalse = refl
    }

canonicalActiveDysfunctionAssessment : StressPhaseAssessment
canonicalActiveDysfunctionAssessment =
  record
    { assessmentId = "canonical active-dysfunction candidate"
    ; phase = activeDysfunctionPhase
    ; signedRegime = Trit.sspNegOne
    ; observations = canonicalStressObservation ∷ []
    ; linkedBasinRegion = Basin.badBasinRegion
    ; phaseDigest = "active dysfunction requires market-function receipts"
    ; replayReceiptId = "missing active-dysfunction replay receipt"
    ; replayReceiptSupplied = false
    ; replayReceiptSuppliedIsFalseByDefault = refl
    ; deterministicCountdownClaim = false
    ; deterministicCountdownClaimIsFalse = refl
    ; sovereignCrisisClaim = false
    ; sovereignCrisisClaimIsFalse = refl
    }

canonicalStabilizationAssessment : StressPhaseAssessment
canonicalStabilizationAssessment =
  record
    { assessmentId = "canonical stabilization candidate"
    ; phase = stabilizationPhase
    ; signedRegime = Trit.sspPosOne
    ; observations = canonicalStressObservation ∷ []
    ; linkedBasinRegion = Basin.goodBasinRegion
    ; phaseDigest = "stabilization requires normalized funding/function receipts"
    ; replayReceiptId = "missing stabilization replay receipt"
    ; replayReceiptSupplied = false
    ; replayReceiptSuppliedIsFalseByDefault = refl
    ; deterministicCountdownClaim = false
    ; deterministicCountdownClaimIsFalse = refl
    ; sovereignCrisisClaim = false
    ; sovereignCrisisClaimIsFalse = refl
    }

------------------------------------------------------------------------
-- BAD windows and event/news alignment.
--
-- A window is delimited by adverse-regime onsets.  The interval may contain
-- adverse, neutral, or favorable substructure; the carrier records the
-- inter-onset geometry without asserting that every point in it is adverse.

data WindowBoundaryKind : Set where
  adverseOnsetBoundary : WindowBoundaryKind
  adverseExitBoundary : WindowBoundaryKind
  nextAdverseOnsetBoundary : WindowBoundaryKind
  datasetBoundary : WindowBoundaryKind

record AdverseInterarrivalWindow : Set where
  field
    windowId : String
    startBoundary : WindowBoundaryKind
    endBoundary : WindowBoundaryKind
    startTimestamp : String
    endTimestamp : String
    signedPeakRegime : Trit.SSPTrit
    phaseAssessment : StressPhaseAssessment
    eventCountDigest : String
    maximumSeverityDigest : String
    persistenceDigest : String
    sourceReplayReceiptId : String
    sourceReplayReceiptSupplied : Bool
    sourceReplayReceiptSuppliedIsFalseByDefault :
      sourceReplayReceiptSupplied ≡ false
    completeCalendarCoverage : Bool
    completeCalendarCoverageIsFalseByDefault :
      completeCalendarCoverage ≡ false

open AdverseInterarrivalWindow public

canonicalAdverseInterarrivalWindow : AdverseInterarrivalWindow
canonicalAdverseInterarrivalWindow =
  record
    { windowId = "canonical adverse-onset interarrival window"
    ; startBoundary = adverseOnsetBoundary
    ; endBoundary = nextAdverseOnsetBoundary
    ; startTimestamp = "unavailable"
    ; endTimestamp = "unavailable"
    ; signedPeakRegime = Trit.sspNegOne
    ; phaseAssessment = canonicalActiveDysfunctionAssessment
    ; eventCountDigest = "event count unavailable"
    ; maximumSeverityDigest = "severity unavailable"
    ; persistenceDigest = "persistence unavailable"
    ; sourceReplayReceiptId = "missing interarrival-window replay receipt"
    ; sourceReplayReceiptSupplied = false
    ; sourceReplayReceiptSuppliedIsFalseByDefault = refl
    ; completeCalendarCoverage = false
    ; completeCalendarCoverageIsFalseByDefault = refl
    }

data ScenarioAttribution : Set where
  genericRiskStressAttribution : ScenarioAttribution
  sovereignFundingStressAttribution : ScenarioAttribution
  technologyDurationStressAttribution : ScenarioAttribution
  aiCapexStressAttribution : ScenarioAttribution
  treasuryLiquidityStressAttribution : ScenarioAttribution
  mixedStressAttribution : ScenarioAttribution
  unattributedStress : ScenarioAttribution

record ScenarioAttributionCandidate : Set where
  field
    attributionId : String
    adverseWindow : AdverseInterarrivalWindow
    attribution : ScenarioAttribution
    supportingAxes : List StressAxis
    newsWindowDigest : String
    newsProviderDigest : String
    newsReceiptId : String
    newsReceiptSupplied : Bool
    newsReceiptSuppliedIsFalseByDefault :
      newsReceiptSupplied ≡ false
    postHocAlignmentOnly : Bool
    postHocAlignmentOnlyIsTrue : postHocAlignmentOnly ≡ true
    causalAttributionPromoted : Bool
    causalAttributionPromotedIsFalse :
      causalAttributionPromoted ≡ false
    headlinePredictionPromoted : Bool
    headlinePredictionPromotedIsFalse :
      headlinePredictionPromoted ≡ false

open ScenarioAttributionCandidate public

canonicalGreeceStyleAttributionCandidate : ScenarioAttributionCandidate
canonicalGreeceStyleAttributionCandidate =
  record
    { attributionId = "Greece-style sovereign/funding stress fixture"
    ; adverseWindow = canonicalAdverseInterarrivalWindow
    ; attribution = sovereignFundingStressAttribution
    ; supportingAxes =
        fundingStressAxis
        ∷ correlationStressAxis
        ∷ narrativeInstabilityAxis
        ∷ treasuryFunctioningAxis
        ∷ []
    ; newsWindowDigest =
        "mid-July-2015-style news alignment is a replay fixture only"
    ; newsProviderDigest = "provider/date coverage must be receipted"
    ; newsReceiptId = "missing Greece-style alignment receipt"
    ; newsReceiptSupplied = false
    ; newsReceiptSuppliedIsFalseByDefault = refl
    ; postHocAlignmentOnly = true
    ; postHocAlignmentOnlyIsTrue = refl
    ; causalAttributionPromoted = false
    ; causalAttributionPromotedIsFalse = refl
    ; headlinePredictionPromoted = false
    ; headlinePredictionPromotedIsFalse = refl
    }

canonicalAIStressAttributionCandidate : ScenarioAttributionCandidate
canonicalAIStressAttributionCandidate =
  record
    { attributionId = "AI-capex/technology-duration stress candidate"
    ; adverseWindow = canonicalAdverseInterarrivalWindow
    ; attribution = aiCapexStressAttribution
    ; supportingAxes =
        technologyConcentrationAxis
        ∷ capexRevisionAxis
        ∷ secondaryHardwareMarketAxis
        ∷ powerAndCoolingConstraintAxis
        ∷ fundingStressAxis
        ∷ creditTransmissionAxis
        ∷ []
    ; newsWindowDigest =
        "AI scenario requires concentration and transmission receipts"
    ; newsProviderDigest = "news is corroboration, not the detector"
    ; newsReceiptId = "missing AI-stress attribution receipt"
    ; newsReceiptSupplied = false
    ; newsReceiptSuppliedIsFalseByDefault = refl
    ; postHocAlignmentOnly = true
    ; postHocAlignmentOnlyIsTrue = refl
    ; causalAttributionPromoted = false
    ; causalAttributionPromotedIsFalse = refl
    ; headlinePredictionPromoted = false
    ; headlinePredictionPromotedIsFalse = refl
    }

------------------------------------------------------------------------
-- Cross-layer machine and hard non-promotion boundary.

record TechSystemicStressMachine : Set where
  field
    machineId : String
    incomingEvidence : Trading.IncomingEvidenceBraid
    stressObservations : List StressAxisObservation
    phaseAssessment : StressPhaseAssessment
    signedRegime : Trit.SSPTrit
    postureBoundary : PostureExecutionBoundary
    adverseWindow : AdverseInterarrivalWindow
    scenarioAttribution : ScenarioAttributionCandidate
    empiricalValidationSurface : Basin.FieldWindowFeature
    observationClassificationPostureExecutionSeparated : Bool
    observationClassificationPostureExecutionSeparatedIsTrue :
      observationClassificationPostureExecutionSeparated ≡ true
    signedRegimeIsNotPriceDirection : Bool
    signedRegimeIsNotPriceDirectionIsTrue :
      signedRegimeIsNotPriceDirection ≡ true
    marketPredictionAuthority : Bool
    marketPredictionAuthorityIsFalse :
      marketPredictionAuthority ≡ false
    financialAdviceAuthority : Bool
    financialAdviceAuthorityIsFalse :
      financialAdviceAuthority ≡ false
    productionExecutionAuthority : Bool
    productionExecutionAuthorityIsFalse :
      productionExecutionAuthority ≡ false

open TechSystemicStressMachine public

canonicalTechSystemicStressMachine : TechSystemicStressMachine
canonicalTechSystemicStressMachine =
  record
    { machineId = "canonical candidate-only tech/systemic stress machine"
    ; incomingEvidence = Trading.canonicalIncomingEvidenceBraid
    ; stressObservations = canonicalStressObservation ∷ []
    ; phaseAssessment = canonicalActiveDysfunctionAssessment
    ; signedRegime = Trit.sspNegOne
    ; postureBoundary = canonicalDefensiveBoundary
    ; adverseWindow = canonicalAdverseInterarrivalWindow
    ; scenarioAttribution = canonicalAIStressAttributionCandidate
    ; empiricalValidationSurface = Basin.canonicalFieldWindowFeature
    ; observationClassificationPostureExecutionSeparated = true
    ; observationClassificationPostureExecutionSeparatedIsTrue = refl
    ; signedRegimeIsNotPriceDirection = true
    ; signedRegimeIsNotPriceDirectionIsTrue = refl
    ; marketPredictionAuthority = false
    ; marketPredictionAuthorityIsFalse = refl
    ; financialAdviceAuthority = false
    ; financialAdviceAuthorityIsFalse = refl
    ; productionExecutionAuthority = false
    ; productionExecutionAuthorityIsFalse = refl
    }

techSystemicStressBoundarySummary : String
techSystemicStressBoundarySummary =
  "Signed {-1,0,+1} structural regimes feed separate capital postures and bounded execution families; stress phases, adverse-onset windows, news alignment, and tech/sovereign attribution remain receipt-gated, candidate-only, and non-predictive."
