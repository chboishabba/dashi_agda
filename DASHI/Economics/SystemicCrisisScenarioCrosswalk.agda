module DASHI.Economics.SystemicCrisisScenarioCrosswalk where

open import DASHI.Core.Prelude
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Promotion.TechSystemicStressScenarioBoundary as Scenario
import DASHI.Economics.SystemicCrisisSignalKernel as Crisis
import DASHI.Economics.SystemicCrisisCompressionBridge as Compression

------------------------------------------------------------------------
-- Cross-pollination boundary.
--
-- The Promotion tranche provides source-bound scenario observations,
-- empirical-basin links, adverse interarrival windows, capital posture, and
-- fail-closed execution governance.  The Economics tranche provides an
-- executable plumbing classifier, hysteresis, an explicit transmission chain,
-- quotient/residual fracture, and MDL promotion gates.
--
-- This module relates those surfaces without identifying them.  In particular:
--   * structural sign is not price direction;
--   * phase classification is not execution authority;
--   * scenario attribution is not causal proof;
--   * unresolved evidence is not silently classified as normal.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Exact carrier isomorphism between the two existing signed trit surfaces.
------------------------------------------------------------------------

sspToCore : SSP.SSPTrit → Trit
sspToCore SSP.sspNegOne = neg
sspToCore SSP.sspZero   = zer
sspToCore SSP.sspPosOne = pos

coreToSSP : Trit → SSP.SSPTrit
coreToSSP neg = SSP.sspNegOne
coreToSSP zer = SSP.sspZero
coreToSSP pos = SSP.sspPosOne

sspCoreRoundTrip : (t : SSP.SSPTrit) → coreToSSP (sspToCore t) ≡ t
sspCoreRoundTrip SSP.sspNegOne = refl
sspCoreRoundTrip SSP.sspZero   = refl
sspCoreRoundTrip SSP.sspPosOne = refl

coreSSPRoundTrip : (t : Trit) → sspToCore (coreToSSP t) ≡ t
coreSSPRoundTrip neg = refl
coreSSPRoundTrip zer = refl
coreSSPRoundTrip pos = refl

------------------------------------------------------------------------
-- Phase crosswalk is deliberately partial.
--
-- `unresolvedPhase` carries insufficient evidence and therefore has no
-- mechanism phase.  It must not be mapped to `normalPhase` merely to obtain a
-- total function.
------------------------------------------------------------------------

data MaybePhase : Set where
  noMechanismPhase : MaybePhase
  mechanismPhase   : Crisis.CrisisPhase → MaybePhase

scenarioPhaseToMechanism : Scenario.StressPhase → MaybePhase
scenarioPhaseToMechanism Scenario.latentFragilityPhase   = mechanismPhase Crisis.fragilityPhase
scenarioPhaseToMechanism Scenario.triggerProximityPhase  = mechanismPhase Crisis.proximityPhase
scenarioPhaseToMechanism Scenario.activeDysfunctionPhase = mechanismPhase Crisis.activePhase
scenarioPhaseToMechanism Scenario.stabilizationPhase     = mechanismPhase Crisis.abatingPhase
scenarioPhaseToMechanism Scenario.unresolvedPhase        = noMechanismPhase

unresolvedDoesNotBecomeNormal :
  scenarioPhaseToMechanism Scenario.unresolvedPhase ≡ noMechanismPhase
unresolvedDoesNotBecomeNormal = refl

------------------------------------------------------------------------
-- Structural regimes and mechanism phases answer different questions.
------------------------------------------------------------------------

record CrosswalkAssessment : Set where
  constructor crosswalkAssessment
  field
    structuralRegime : SSP.SSPTrit
    scenarioPhase    : Scenario.StressPhase
    mechanismPhase   : MaybePhase
    compressionRegime : Compression.CompressionRegime
    capitalPosture   : Scenario.CapitalPosture
    monitoringPosture : Compression.MonitoringPosture
    phaseCrosswalkAgrees :
      mechanismPhase ≡ scenarioPhaseToMechanism scenarioPhase
    postureCrosswalkAgrees :
      capitalPosture ≡ Scenario.postureFromRegime structuralRegime

open CrosswalkAssessment public

------------------------------------------------------------------------
-- Monitoring posture depends on mechanism evidence and model fracture.
-- Capital posture remains the separately governed scenario-layer output.
------------------------------------------------------------------------

monitoringFromScenario :
  Scenario.StressPhase → Compression.CompressionRegime → Compression.MonitoringPosture
monitoringFromScenario Scenario.latentFragilityPhase r =
  Compression.monitoringPosture Crisis.fragilityPhase r
monitoringFromScenario Scenario.triggerProximityPhase r =
  Compression.monitoringPosture Crisis.proximityPhase r
monitoringFromScenario Scenario.activeDysfunctionPhase r =
  Compression.monitoringPosture Crisis.activePhase r
monitoringFromScenario Scenario.stabilizationPhase r =
  Compression.monitoringPosture Crisis.abatingPhase r
monitoringFromScenario Scenario.unresolvedPhase r = Compression.modelReview

mkCrosswalkAssessment :
  SSP.SSPTrit → Scenario.StressPhase → Compression.CompressionRegime →
  CrosswalkAssessment
mkCrosswalkAssessment signed phase compression =
  crosswalkAssessment
    signed
    phase
    (scenarioPhaseToMechanism phase)
    compression
    (Scenario.postureFromRegime signed)
    (monitoringFromScenario phase compression)
    refl
    refl

------------------------------------------------------------------------
-- Observation-axis crosswalk.
--
-- The scenario module has a broader source taxonomy.  Only axes with a direct
-- plumbing interpretation are projected into the mechanism kernel.  Narrative,
-- execution churn, technology concentration, capex, hardware, and power/cooling
-- remain explanatory/candidate axes until a separate transmission receipt links
-- them to funding, liquidity, contagion, or forced selling.
------------------------------------------------------------------------

data MechanismAxis : Set where
  fundingMechanismAxis      : MechanismAxis
  liquidityMechanismAxis    : MechanismAxis
  contagionMechanismAxis    : MechanismAxis
  treasuryFunctionAxis      : MechanismAxis
  creditTransmissionAxis    : MechanismAxis
  candidateExplanatoryAxis  : MechanismAxis

stressAxisToMechanismAxis : Scenario.StressAxis → MechanismAxis
stressAxisToMechanismAxis Scenario.fundingStressAxis = fundingMechanismAxis
stressAxisToMechanismAxis Scenario.liquidityStressAxis = liquidityMechanismAxis
stressAxisToMechanismAxis Scenario.correlationStressAxis = contagionMechanismAxis
stressAxisToMechanismAxis Scenario.treasuryFunctioningAxis = treasuryFunctionAxis
stressAxisToMechanismAxis Scenario.creditTransmissionAxis = creditTransmissionAxis
stressAxisToMechanismAxis Scenario.narrativeInstabilityAxis = candidateExplanatoryAxis
stressAxisToMechanismAxis Scenario.executionChurnAxis = candidateExplanatoryAxis
stressAxisToMechanismAxis Scenario.technologyConcentrationAxis = candidateExplanatoryAxis
stressAxisToMechanismAxis Scenario.capexRevisionAxis = candidateExplanatoryAxis
stressAxisToMechanismAxis Scenario.secondaryHardwareMarketAxis = candidateExplanatoryAxis
stressAxisToMechanismAxis Scenario.powerAndCoolingConstraintAxis = candidateExplanatoryAxis

technologyConcentrationIsNotFundingReceipt :
  stressAxisToMechanismAxis Scenario.technologyConcentrationAxis
  ≡ candidateExplanatoryAxis
technologyConcentrationIsNotFundingReceipt = refl

------------------------------------------------------------------------
-- Interarrival windows contribute temporal geometry, not causal attribution.
------------------------------------------------------------------------

record WindowBridgeReceipt : Set where
  constructor windowBridgeReceipt
  field
    window : Scenario.AdverseInterarrivalWindow
    residualProfile : Compression.ResidualDepthProfile
    sourceReplayClosed : Bool
    calendarCoverageClosed : Bool
    noCausalPromotion : Bool
    noExecutionPromotion : Bool

open WindowBridgeReceipt public

windowBridgeClosed : WindowBridgeReceipt → Bool
windowBridgeClosed r =
  sourceReplayClosed r
  ∧ calendarCoverageClosed r
  ∧ noCausalPromotion r
  ∧ noExecutionPromotion r

------------------------------------------------------------------------
-- Execution remains fail-closed after crosswalk.
------------------------------------------------------------------------

record CrosswalkGovernance : Set where
  constructor crosswalkGovernance
  field
    observationClassificationSeparated : Bool
    classificationPostureSeparated      : Bool
    postureExecutionSeparated           : Bool
    adverseIsNotAutomaticShort          : Bool
    arbitrarySignInversionRejected      : Bool
    productionExecutionAuthorityAbsent  : Bool

open CrosswalkGovernance public

crosswalkGovernanceClosed : CrosswalkGovernance → Bool
crosswalkGovernanceClosed g =
  observationClassificationSeparated g
  ∧ classificationPostureSeparated g
  ∧ postureExecutionSeparated g
  ∧ adverseIsNotAutomaticShort g
  ∧ arbitrarySignInversionRejected g
  ∧ productionExecutionAuthorityAbsent g

canonicalCrosswalkGovernance : CrosswalkGovernance
canonicalCrosswalkGovernance =
  crosswalkGovernance true true true true true true

canonicalCrosswalkGovernanceClosed :
  crosswalkGovernanceClosed canonicalCrosswalkGovernance ≡ true
canonicalCrosswalkGovernanceClosed = refl
