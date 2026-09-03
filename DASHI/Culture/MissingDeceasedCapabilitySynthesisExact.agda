module DASHI.Culture.MissingDeceasedCapabilitySynthesisExact where

------------------------------------------------------------------------
-- CAPABILITY SYNTHESIS OVER THE MISSING/DECEASED TECHNICAL-WORK ATLAS
--
-- This fixture asks: what higher-order engineering capabilities could integrate
-- the documented knowledge domains represented across the roster?
--
-- It does NOT assert that these people collaborated, that one programme joined
-- their work, or that any death/disappearance was caused by these capabilities.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.CapabilitySynthesisHypergraphExact as C

------------------------------------------------------------------------
-- 1. High-power deep-space transport / fusion-spacecraft architecture.
--
-- NASA publicly documents both fission-based nuclear thermal/electric propulsion
-- and fusion-propulsion concepts.  The interface therefore exists independently
-- of this roster.
-- Sources:
-- NASA Space Nuclear Propulsion, current programme page.
-- NASA NIAC: Nuclear Propulsion Through Direct Conversion of Fusion Energy.
-- NASA NIAC/TechPort: Advanced Fusion Power and Thrust Generation with
-- Centrifugally Confined Plasmas.
------------------------------------------------------------------------

highPowerDeepSpaceTransport : C.CapabilitySynthesis
highPowerDeepSpaceTransport = C.capability-synthesis
  C.deepSpaceHighPowerTransport
  (C.fusionPhysics ∷
   C.highEnergyPlasmaPhysics ∷
   C.fissionPowerAndPropulsion ∷
   C.extremeEnvironmentMaterials ∷
   C.spacecraftSystemsEngineering ∷ [])
  C.documentedProgrammeConcept
  "NASA Space Nuclear Propulsion; NASA NIAC fusion-propulsion studies; NASA ESI fusion power/thrust studies"
  "A source-backed engineering design space combines nuclear/fusion energy, magnetized plasma, extreme-temperature materials, and spacecraft integration for high-specific-power deep-space transport."

------------------------------------------------------------------------
-- 2. Autonomous high-energy planetary interceptor / defense spacecraft.
--
-- This is a cross-domain engineering inference rather than a claim that one
-- roster programme exists: high-energy propulsion/power + guidance/navigation +
-- planetary-defense target characterization + robust spacecraft materials.
------------------------------------------------------------------------

autonomousPlanetaryInterceptor : C.CapabilitySynthesis
autonomousPlanetaryInterceptor = C.capability-synthesis
  C.autonomousPlanetaryInterceptor
  (C.fissionPowerAndPropulsion ∷
   C.extremeEnvironmentMaterials ∷
   C.navigationGuidanceAndTracking ∷
   C.planetaryDefenseAndNEOScience ∷
   C.spacecraftSystemsEngineering ∷ [])
  C.crossDomainEngineeringInference
  "NASA nuclear propulsion mission-enablement material + DART/NEO planetary-defense domain + general spacecraft guidance/navigation engineering"
  "A high-energy, long-endurance spacecraft could in principle combine rapid transport, autonomous navigation, and planetary interception/characterization. This is capability synthesis, not evidence that Hicks, LeBlanc, Reza or McCasland shared a programme."

------------------------------------------------------------------------
-- 3. Long-duration, high-power science platform.
------------------------------------------------------------------------

longDurationSciencePlatform : C.CapabilitySynthesis
longDurationSciencePlatform = C.capability-synthesis
  C.longDurationSciencePlatform
  (C.fissionPowerAndPropulsion ∷
   C.planetaryMassSpectrometryAndBiosignatures ∷
   C.astronomicalRemoteSensing ∷
   C.planetaryDefenseAndNEOScience ∷
   C.spacecraftSystemsEngineering ∷ [])
  C.crossDomainEngineeringInference
  "NASA SNP states that nuclear systems can provide years of solar-independent power and enable more capable deep-space instruments and communications"
  "The scientifically strongest benign synthesis is a long-lived outer-solar-system platform carrying high-power sensing, spectroscopy, astronomical and planetary-science payloads where solar power is inadequate."

------------------------------------------------------------------------
-- 4. High-energy test, validation, and diagnostics ecosystem.
--
-- DARHT/Scorpius contributes accelerator/radiographic diagnostics; fusion/plasma
-- development independently depends on diagnostics/computation/materials.  This
-- synthesis captures a research/test ecosystem, not an onboard spacecraft.
------------------------------------------------------------------------

highEnergyDiagnosticsEcosystem : C.CapabilitySynthesis
highEnergyDiagnosticsEcosystem = C.capability-synthesis
  C.highEnergyTestAndDiagnosticsEcosystem
  (C.acceleratorRadiographyDiagnostics ∷
   C.highEnergyPlasmaPhysics ∷
   C.fusionPhysics ∷
   C.extremeEnvironmentMaterials ∷ [])
  C.crossDomainEngineeringInference
  "LANL/NNSA Scorpius-DARHT radiography descriptions + NASA/NTRS fusion-propulsion literature noting common plasma/fusion physics, enabling technologies, computation and diagnostics"
  "A powerful integration is not necessarily one vehicle: it can be a test-and-validation stack for extreme energy-density systems, combining radiographic diagnostics, plasma modeling and extreme-environment material qualification."

------------------------------------------------------------------------
-- 5. Extreme-environment high-power space platform.
--
-- The integration of hot/oxidizing-environment materials with nuclear/fusion
-- power and spacecraft/payload engineering is a documented engineering problem.
------------------------------------------------------------------------

extremeEnvironmentSpacePlatform : C.CapabilitySynthesis
extremeEnvironmentSpacePlatform = C.capability-synthesis
  C.extremeEnvironmentSpacePlatform
  (C.extremeEnvironmentMaterials ∷
   C.fissionPowerAndPropulsion ∷
   C.highEnergyPlasmaPhysics ∷
   C.spacecraftSystemsEngineering ∷
   C.highPowerPayloadIntegration ∷ [])
  C.crossDomainEngineeringInference
  "NASA SNP identifies reactor material temperatures as a central constraint; Reza/Jacinto patent independently addresses burn-resistant high-strength alloys for oxygen-rich environments"
  "Extreme-temperature materials, high-density power and payload integration naturally cohabit advanced space-system design, though no same-object programme linking the roster is asserted."

------------------------------------------------------------------------
-- Current strongest synthesis assessment.
------------------------------------------------------------------------

record CapabilityFrontierAssessment : Set where
  constructor capability-frontier-assessment
  field
    fusionAndSpaceAreDocumentedEngineeringInterface : Bool
    fusionAndSpaceAreDocumentedEngineeringInterfaceIsTrue :
      fusionAndSpaceAreDocumentedEngineeringInterface ≡ true

    nuclearPowerCanSupportLongDurationHighPowerSpacecraft : Bool
    nuclearPowerCanSupportLongDurationHighPowerSpacecraftIsTrue :
      nuclearPowerCanSupportLongDurationHighPowerSpacecraft ≡ true

    rosterWorkCanBeMappedIntoHigherOrderCapabilityStacks : Bool
    rosterWorkCanBeMappedIntoHigherOrderCapabilityStacksIsTrue :
      rosterWorkCanBeMappedIntoHigherOrderCapabilityStacks ≡ true

    mappingImpliesHistoricalCommonProgramme : Bool
    mappingImpliesHistoricalCommonProgrammeIsFalse :
      mappingImpliesHistoricalCommonProgramme ≡ false

    mostPowerfulSynthesisImpliesReasonForSelection : Bool
    mostPowerfulSynthesisImpliesReasonForSelectionIsFalse :
      mostPowerfulSynthesisImpliesReasonForSelection ≡ false

canonicalCapabilityFrontierAssessment : CapabilityFrontierAssessment
canonicalCapabilityFrontierAssessment = capability-frontier-assessment
  true refl
  true refl
  true refl
  false refl
  false refl
