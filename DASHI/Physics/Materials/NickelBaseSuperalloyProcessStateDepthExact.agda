module DASHI.Physics.Materials.NickelBaseSuperalloyProcessStateDepthExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

-- Generic process -> microstructure -> property owner for Ni-base superalloys.
-- Sources:
-- Samuel J. Galpin, "A review of microstructure phenomena during manufacture of polycrystalline Ni-based superalloys",
-- Materials Science and Technology 38(16), 2022, DOI 10.1080/02670836.2022.2069332.
-- N. D'Souza et al., "On the Evolution of Primary Gamma Prime Precipitates During High Temperature and High Strain Rate Deformation and Subsequent Heat Treatment in the Ni-Based Superalloy, RR1000",
-- Metallurgical and Materials Transactions A 50, 4205-4222 (2019), DOI 10.1007/s11661-019-05330-w.
-- Yao et al., "Effect of rejuvenation heat treatments on gamma prime distributions in a Ni based superalloy for power plant applications",
-- Materials Science and Technology 29(7), 2013, DOI 10.1179/1743284712Y.0000000199.

data ProcessCoordinate : Set where
  solutionTemperature : ProcessCoordinate
  solutionTime : ProcessCoordinate
  coolingRate : ProcessCoordinate
  ageingTemperature : ProcessCoordinate
  ageingTime : ProcessCoordinate
  deformationTemperature : ProcessCoordinate
  strainRate : ProcessCoordinate
  totalStrain : ProcessCoordinate
  remeltHistory : ProcessCoordinate

data MicrostructureCoordinate : Set where
  gammaGrainSize : MicrostructureCoordinate
  primaryGammaPrime : MicrostructureCoordinate
  secondaryGammaPrime : MicrostructureCoordinate
  tertiaryGammaPrime : MicrostructureCoordinate
  gammaPrimeVolumeFraction : MicrostructureCoordinate
  precipitateCoherency : MicrostructureCoordinate
  segregation : MicrostructureCoordinate
  porosity : MicrostructureCoordinate
  tcpPhasePopulation : MicrostructureCoordinate
  grainBoundaryState : MicrostructureCoordinate

data PropertyCoordinate : Set where
  yieldStrength : PropertyCoordinate
  tensileStrength : PropertyCoordinate
  creepResistance : PropertyCoordinate
  hardness : PropertyCoordinate
  fatigueResistance : PropertyCoordinate
  oxidationResistance : PropertyCoordinate
  burnResistance : PropertyCoordinate
  ductility : PropertyCoordinate

record ProcessState : Set where
  constructor process-state
  field
    processHistory : List ProcessCoordinate
    microstructureState : List MicrostructureCoordinate
    targetProperties : List PropertyCoordinate
    sourceReference : String
    boundedReading : String

open ProcessState public

canonicalProcessState : ProcessState
canonicalProcessState = process-state
  (solutionTemperature ∷ solutionTime ∷ coolingRate ∷ ageingTemperature ∷ ageingTime ∷ deformationTemperature ∷ strainRate ∷ totalStrain ∷ [])
  (gammaGrainSize ∷ primaryGammaPrime ∷ secondaryGammaPrime ∷ tertiaryGammaPrime ∷ gammaPrimeVolumeFraction ∷ precipitateCoherency ∷ segregation ∷ tcpPhasePopulation ∷ grainBoundaryState ∷ [])
  (yieldStrength ∷ tensileStrength ∷ creepResistance ∷ fatigueResistance ∷ ductility ∷ [])
  "Galpin 2022 DOI 10.1080/02670836.2022.2069332; D'Souza et al. 2019 DOI 10.1007/s11661-019-05330-w; Yao et al. 2013 DOI 10.1179/1743284712Y.0000000199"
  "Heat treatment and thermomechanical history govern gamma/gamma-prime morphology, recrystallisation, TCP phases and related mechanical properties; nominal chemistry alone is not a sufficient state description."

record ProcessStateBoundary : Set where
  constructor process-state-boundary
  field
    sameNominalCompositionImpliesSameMicrostructure : Bool
    sameNominalCompositionImpliesSameMicrostructureIsFalse : sameNominalCompositionImpliesSameMicrostructure ≡ false
    sameMicrostructureImpliesSamePropertyAtAllTemperatures : Bool
    sameMicrostructureImpliesSamePropertyAtAllTemperaturesIsFalse : sameMicrostructureImpliesSamePropertyAtAllTemperatures ≡ false
    heatTreatmentCanAlterGammaPrimeDistribution : Bool
    heatTreatmentCanAlterGammaPrimeDistributionIsTrue : heatTreatmentCanAlterGammaPrimeDistribution ≡ true
    deformationHistoryCanAlterRecrystallisationAndGammaPrimeState : Bool
    deformationHistoryCanAlterRecrystallisationAndGammaPrimeStateIsTrue : deformationHistoryCanAlterRecrystallisationAndGammaPrimeState ≡ true

open ProcessStateBoundary public

canonicalProcessStateBoundary : ProcessStateBoundary
canonicalProcessStateBoundary = process-state-boundary false refl false refl true refl true refl

data ProcessStateReverseTarget : Set where
  acquireExactHeatTreatmentSchedule : ProcessStateReverseTarget
  acquireThermomechanicalHistory : ProcessStateReverseTarget
  acquireGammaPrimeSizeDistribution : ProcessStateReverseTarget
  acquireGammaPrimeVolumeFraction : ProcessStateReverseTarget
  acquireGrainSizeAndBoundaryState : ProcessStateReverseTarget
  acquireSegregationAndPorosity : ProcessStateReverseTarget
  acquireTCPPhaseCharacterisation : ProcessStateReverseTarget
  acquireTemperatureResolvedPropertyData : ProcessStateReverseTarget
