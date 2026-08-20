module DASHI.Economics.SystemicCrisisScenarioCrosswalkTests where

open import DASHI.Core.Prelude
open import DASHI.Algebra.Trit using (neg; zer; pos)

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Promotion.TechSystemicStressScenarioBoundary as Scenario
import DASHI.Economics.SystemicCrisisSignalKernel as Crisis
import DASHI.Economics.SystemicCrisisCompressionBridge as Compression
import DASHI.Economics.SystemicCrisisScenarioCrosswalk as Crosswalk

carrierNegRoundTrip :
  Crosswalk.coreToSSP (Crosswalk.sspToCore SSP.sspNegOne) ≡ SSP.sspNegOne
carrierNegRoundTrip = refl

carrierZeroRoundTrip :
  Crosswalk.sspToCore (Crosswalk.coreToSSP zer) ≡ zer
carrierZeroRoundTrip = refl

latentMapsToFragility :
  Crosswalk.scenarioPhaseToMechanism Scenario.latentFragilityPhase
  ≡ Crosswalk.mechanismPhase Crisis.fragilityPhase
latentMapsToFragility = refl

activeMapsToActive :
  Crosswalk.scenarioPhaseToMechanism Scenario.activeDysfunctionPhase
  ≡ Crosswalk.mechanismPhase Crisis.activePhase
activeMapsToActive = refl

stabilizationMapsToAbating :
  Crosswalk.scenarioPhaseToMechanism Scenario.stabilizationPhase
  ≡ Crosswalk.mechanismPhase Crisis.abatingPhase
stabilizationMapsToAbating = refl

unresolvedRemainsUnresolved :
  Crosswalk.scenarioPhaseToMechanism Scenario.unresolvedPhase
  ≡ Crosswalk.noMechanismPhase
unresolvedRemainsUnresolved = refl

technologyAxisRemainsCandidate :
  Crosswalk.stressAxisToMechanismAxis Scenario.technologyConcentrationAxis
  ≡ Crosswalk.candidateExplanatoryAxis
technologyAxisRemainsCandidate = refl

fundingAxisProjectsDirectly :
  Crosswalk.stressAxisToMechanismAxis Scenario.fundingStressAxis
  ≡ Crosswalk.fundingMechanismAxis
fundingAxisProjectsDirectly = refl

activeMonitoringDominates :
  Crosswalk.monitoringFromScenario
    Scenario.activeDysfunctionPhase Compression.compressiveRegime
  ≡ Compression.activeDysfunction
activeMonitoringDominates = refl

unresolvedRequestsModelReview :
  Crosswalk.monitoringFromScenario
    Scenario.unresolvedPhase Compression.compressiveRegime
  ≡ Compression.modelReview
unresolvedRequestsModelReview = refl

canonicalAssessment : Crosswalk.CrosswalkAssessment
canonicalAssessment =
  Crosswalk.mkCrosswalkAssessment
    SSP.sspNegOne
    Scenario.activeDysfunctionPhase
    Compression.fractureRegime

canonicalAssessmentPhase :
  Crosswalk.CrosswalkAssessment.mechanismPhase canonicalAssessment
  ≡ Crosswalk.mechanismPhase Crisis.activePhase
canonicalAssessmentPhase = refl

canonicalAssessmentCapitalPosture :
  Crosswalk.CrosswalkAssessment.capitalPosture canonicalAssessment
  ≡ Scenario.defensivePosture
canonicalAssessmentCapitalPosture = refl

canonicalGovernanceClosed :
  Crosswalk.crosswalkGovernanceClosed Crosswalk.canonicalCrosswalkGovernance
  ≡ true
canonicalGovernanceClosed = refl
