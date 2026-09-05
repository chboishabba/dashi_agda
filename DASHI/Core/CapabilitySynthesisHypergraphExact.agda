module DASHI.Core.CapabilitySynthesisHypergraphExact where

------------------------------------------------------------------------
-- CAPABILITY-SYNTHESIS HYPERGRAPH
--
-- Purpose: distinguish three questions that must not be collapsed:
--   (1) what knowledge/technology fibres exist;
--   (2) what higher-order capability could integrate those fibres;
--   (3) whether any particular historical people/programmes were in fact
--       assembled into that capability.
--
-- This module is intentionally system-level.  It models capability composition
-- and evidentiary status; it does not encode operational weapon construction.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Knowledge fibres and synthesis outputs.
------------------------------------------------------------------------

data KnowledgeDomain : Set where
  highEnergyPlasmaPhysics
  fusionPhysics
  fissionPowerAndPropulsion
  extremeEnvironmentMaterials
  acceleratorRadiographyDiagnostics
  spacecraftSystemsEngineering
  navigationGuidanceAndTracking
  highPowerPayloadIntegration
  planetaryDefenseAndNEOScience
  planetaryMassSpectrometryAndBiosignatures
  astronomicalRemoteSensing
  chemicalBiologyAndLifeScience
  : KnowledgeDomain

data CapabilityClass : Set where
  deepSpaceHighPowerTransport
  fusionOrNuclearElectricSpacecraft
  autonomousPlanetaryInterceptor
  longDurationSciencePlatform
  highEnergyTestAndDiagnosticsEcosystem
  extremeEnvironmentSpacePlatform
  multiMissionStrategicSpaceArchitecture
  unresolvedCapabilityClass
  : CapabilityClass

data SynthesisStrength : Set where
  documentedEngineeringInterface
  documentedProgrammeConcept
  crossDomainEngineeringInference
  speculativeExtrapolation
  : SynthesisStrength

record CapabilitySynthesis : Set where
  constructor capability-synthesis
  field
    capability : CapabilityClass
    inputDomains : List KnowledgeDomain
    strength : SynthesisStrength
    sourceReference : String
    boundedReading : String

open CapabilitySynthesis public

------------------------------------------------------------------------
-- A person/work graph does not prove participation in a synthesized capability.
------------------------------------------------------------------------

record SynthesisBoundary : Set where
  constructor synthesis-boundary
  field
    domainCanParticipateInCapabilityWithoutSharedProgramme : Bool
    domainCanParticipateInCapabilityWithoutSharedProgrammeIsTrue :
      domainCanParticipateInCapabilityWithoutSharedProgramme ≡ true

    documentedEngineeringInterfaceImpliesRosterPeopleCollaborated : Bool
    documentedEngineeringInterfaceImpliesRosterPeopleCollaboratedIsFalse :
      documentedEngineeringInterfaceImpliesRosterPeopleCollaborated ≡ false

    plausibleCapabilityImpliesHistoricalProgrammeExisted : Bool
    plausibleCapabilityImpliesHistoricalProgrammeExistedIsFalse :
      plausibleCapabilityImpliesHistoricalProgrammeExisted ≡ false

    capabilitySynthesisImpliesCommonSelector : Bool
    capabilitySynthesisImpliesCommonSelectorIsFalse :
      capabilitySynthesisImpliesCommonSelector ≡ false

    commonSelectorImpliesCapabilitySynthesis : Bool
    commonSelectorImpliesCapabilitySynthesisIsFalse :
      commonSelectorImpliesCapabilitySynthesis ≡ false

    strongestCapabilityEqualsMostLikelyHistoricalExplanation : Bool
    strongestCapabilityEqualsMostLikelyHistoricalExplanationIsFalse :
      strongestCapabilityEqualsMostLikelyHistoricalExplanation ≡ false

canonicalSynthesisBoundary : SynthesisBoundary
canonicalSynthesisBoundary = synthesis-boundary
  true refl
  false refl
  false refl
  false refl
  false refl
  false refl
