module DASHI.Physics.Foundations.FundamentalConstantViabilityFibreExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.ActiveBidiDiscriminatorLoopExact as Bidi

------------------------------------------------------------------------
-- FUNDAMENTAL-CONSTANT / COSMIC-VIABILITY FIBRE
--
-- This is an experiment/theory-parameter boundary, not a multiverse theorem.
-- Varying parameters inside a model is a counterfactual sensitivity study.
-- It does not assert that every parameter point is physically realised.
--
-- External calibration (not proof authority):
--  * F. C. Adams, JCAP 08 (2008) 010, arXiv:0807.3697: stellar structure over
--    varied G, alpha and nuclear-rate parameters; sizeable stellar region.
--  * F. C. Adams, Phys. Rept. / arXiv:1511.06958: stars + habitable planets
--    over broad alpha/alpha_G ranges.
--  * Epelbaum et al., PRL 110, 112502 (2013): triple-alpha carbon/oxygen
--    sensitivity to light-quark masses and electromagnetic coupling.
------------------------------------------------------------------------

data ParameterCoordinate : Set where
  electromagneticStrength
  gravitationalStrength
  strongInteractionStrength
  weakInteractionStrength
  lightQuarkMass
  electronMass
  vacuumEnergyDensity
  baryonPhotonRatio
  primordialFluctuationAmplitude
  spatialDimension
  : ParameterCoordinate

data ViabilityLayer : Set where
  mathematicalConsistency
  longLivedStructure
  sustainedStars
  nucleosynthesis
  carbonOxygenAvailability
  stableChemistry
  habitableEnvironment
  prebioticOpportunity
  : ViabilityLayer

data ParameterRegionStatus : Set where
  viable unresolved nonviable : ParameterRegionStatus

record ParameterPerturbationReceipt : Set where
  constructor parameter-perturbation-receipt
  field
    baselineParameterReference : String
    variedCoordinateReference : String
    variationRangeReference : String
    equationsHeldFixedReference : String
    correlatedParameterPolicyReference : String
    stellarStructureReference : String
    nucleosynthesisReference : String
    chemistryReference : String
    planetaryEnvironmentReference : String
    nuisanceReference : String
    numericalMethodReference : String
    validationReference : String

activeBidiBoundary : Bidi.ActiveBidiDiscriminatorLoopBoundary
activeBidiBoundary = Bidi.canonicalActiveBidiDiscriminatorLoopBoundary

record FundamentalConstantViabilityBoundary : Set where
  constructor fundamental-constant-viability-boundary
  field
    varyingConstantsInModelProvesOtherUniversesExist : Bool
    varyingConstantsInModelProvesOtherUniversesExistIsFalse :
      varyingConstantsInModelProvesOtherUniversesExist ≡ false
    oneFailedParameterPointProvesObservedConstantsUniquelyNecessary : Bool
    oneFailedParameterPointProvesObservedConstantsUniquelyNecessaryIsFalse :
      oneFailedParameterPointProvesObservedConstantsUniquelyNecessary ≡ false
    oneBroadViableRegionProvesLifeInevitable : Bool
    oneBroadViableRegionProvesLifeInevitableIsFalse :
      oneBroadViableRegionProvesLifeInevitable ≡ false
    stellarViabilityImpliesCarbonOxygenViability : Bool
    stellarViabilityImpliesCarbonOxygenViabilityIsFalse :
      stellarViabilityImpliesCarbonOxygenViability ≡ false
    carbonOxygenViabilityImpliesAbiogenesis : Bool
    carbonOxygenViabilityImpliesAbiogenesisIsFalse :
      carbonOxygenViabilityImpliesAbiogenesis ≡ false
    viableParameterRegionCanBeWiderThanOneObservedPoint : Bool
    viableParameterRegionCanBeWiderThanOneObservedPointIsTrue :
      viableParameterRegionCanBeWiderThanOneObservedPoint ≡ true
    differentViabilityConsumersCanInduceDifferentAllowedRegions : Bool
    differentViabilityConsumersCanInduceDifferentAllowedRegionsIsTrue :
      differentViabilityConsumersCanInduceDifferentAllowedRegions ≡ true
    parameterSensitivityIsAnActiveBidiDiscriminatorProblem : Bool
    parameterSensitivityIsAnActiveBidiDiscriminatorProblemIsTrue :
      parameterSensitivityIsAnActiveBidiDiscriminatorProblem ≡ true
    reading : String

canonicalFundamentalConstantViabilityBoundary : FundamentalConstantViabilityBoundary
canonicalFundamentalConstantViabilityBoundary =
  fundamental-constant-viability-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
    true refl
    true refl
    "Fundamental-parameter variation defines consumer-relative viability fibres. A model may admit broad stellar regions while a narrower carbon/oxygen or chemistry consumer excludes additional points. Counterfactual parameter scans do not establish a realised multiverse, uniqueness of our constants, or inevitability of life."
