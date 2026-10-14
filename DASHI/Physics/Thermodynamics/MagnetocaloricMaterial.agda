module DASHI.Physics.Thermodynamics.MagnetocaloricMaterial where

open import DASHI.Physics.Laws.ThermodynamicStatisticalLaws

------------------------------------------------------------------------
-- Generic magnetocaloric material surface.
--
-- This module deliberately does not assert a Maxwell relation or an
-- adiabatic temperature-change formula for every material.  Those are
-- evidence-bearing law predicates whose validity regime and calibration
-- must be supplied by a material witness.
------------------------------------------------------------------------

record MagnetocaloricMaterial : Set₁ where
  field
    MaterialState       : Set
    Temperature         : Set
    MagneticField       : Set
    Magnetisation       : Set
    Entropy              : Set
    HeatCapacity         : Set
    ThermalConductivity  : Set
    PhaseState           : Set

    temperature          : MaterialState → Temperature
    magneticField        : MaterialState → MagneticField
    magnetisation        : MaterialState → Magnetisation
    entropy              : MaterialState → Entropy
    heatCapacity         : MaterialState → HeatCapacity
    conductivity         : MaterialState → ThermalConductivity
    phaseState           : MaterialState → PhaseState

    OperatingRegime      : MaterialState → Set

record MagnetocaloricResponse
  (M : MagnetocaloricMaterial) : Set₁ where
  open MagnetocaloricMaterial M
  field
    EntropyChange              : Set
    TemperatureChange          : Set
    FieldPath                  : Set

    isothermalEntropyChange :
      Temperature → MagneticField → MagneticField → EntropyChange

    adiabaticTemperatureChange :
      Temperature → MagneticField → MagneticField → TemperatureChange

    followsFieldPath : FieldPath → MaterialState → MaterialState → Set

record MagnetocaloricLaw
  (M : MagnetocaloricMaterial)
  (R : MagnetocaloricResponse M) : Set₁ where
  open MagnetocaloricMaterial M
  open MagnetocaloricResponse R
  field
    MaxwellCompatible : Temperature → MagneticField → Set
    maxwellRelationValid :
      (T : Temperature) (H : MagneticField) → MaxwellCompatible T H

    IsothermalEntropyLaw :
      Temperature → MagneticField → MagneticField → EntropyChange → Set
    isothermalEntropyLaw :
      (T : Temperature) (H₀ H₁ : MagneticField) →
      IsothermalEntropyLaw T H₀ H₁ (isothermalEntropyChange T H₀ H₁)

    AdiabaticResponseLaw :
      Temperature → MagneticField → MagneticField → TemperatureChange → Set
    adiabaticResponseLaw :
      (T : Temperature) (H₀ H₁ : MagneticField) →
      AdiabaticResponseLaw T H₀ H₁
        (adiabaticTemperatureChange T H₀ H₁)

record MagnetocaloricCalibration
  (M : MagnetocaloricMaterial)
  (R : MagnetocaloricResponse M) : Set₁ where
  open MagnetocaloricMaterial M
  field
    CalibrationEvidence : Set
    ConstitutiveFit      : MaterialState → Set
    RegimeValidated      : MaterialState → Set
    calibrationEvidence  : CalibrationEvidence
    constitutiveFit      :
      (s : MaterialState) → OperatingRegime s → ConstitutiveFit s
    regimeValidated      :
      (s : MaterialState) → OperatingRegime s → RegimeValidated s

record MagnetocaloricAuthorityBoundary : Set₁ where
  field
    maxwellRequiresEquilibriumRegularity : Set
    adiabaticChangeRequiresProcessAssumptions : Set
    firstOrderTransitionNeedsCare : Set
    constitutiveValuesRequireCalibration : Set
    materialLawDoesNotProveDeviceCooling : Set
    vendorPerformanceIsNotTheoremAuthority : Set

------------------------------------------------------------------------
-- Crosswalk into the repo-wide thermodynamic law surface.
------------------------------------------------------------------------

record MagnetocaloricThermodynamicCrosswalk
  (T : ThermodynamicStateSpace)
  (M : MagnetocaloricMaterial) : Set₁ where
  field
    StateCompatible       : Set
    TemperatureCompatible : Set
    EntropyCompatible     : Set
    stateCompatible       : StateCompatible
    temperatureCompatible : TemperatureCompatible
    entropyCompatible     : EntropyCompatible
