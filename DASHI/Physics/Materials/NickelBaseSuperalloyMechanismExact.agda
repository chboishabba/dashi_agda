module DASHI.Physics.Materials.NickelBaseSuperalloyMechanismExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- GENERIC NICKEL-BASE SUPERALLOY SCIENCE
--
-- Domain owner beneath alloy-specific patents/fixtures.  It separates
-- composition, processing, microstructure and measured properties so a nominal
-- chemistry cannot definitionally determine realised performance.
------------------------------------------------------------------------

data AlloyMechanism : Set where
  gammaMatrix
  gammaPrimePrecipitation
  solidSolutionStrengthening
  chromiaScaleFormation
  aluminaScaleFormation
  grainBoundaryControl
  solutionHeatTreatment
  ageingHeatTreatment
  vacuumMelting
  remelting
  mechanicalWorking
  : AlloyMechanism

record GammaPrimeSystem : Set where
  constructor gamma-prime-system
  field
    matrixDescription : String
    precipitateDescription : String
    principalFormers : String
    strengtheningMechanism : String
    temperatureDependence : String
    sourceReference : String

open GammaPrimeSystem public

canonicalGammaPrimeSystem : GammaPrimeSystem
canonicalGammaPrimeSystem = gamma-prime-system
  "Ni-rich gamma matrix, face-centred cubic"
  "ordered L1_2 gamma-prime precipitate, approximately Ni3(Al,Ti) in the canonical Ni-base case"
  "Al and Ti"
  "coherent/ordered precipitates impede dislocation motion; antiphase-boundary energy contributes to strengthening"
  "strength depends on precipitate fraction, size, coherency and thermal history; over-ageing/coarsening can change the response"
  "standard nickel-base superalloy metallurgy; gamma-prime Ni3(Al,Ti) precipitation-strengthening literature"

record OxidationProtectionSystem : Set where
  constructor oxidation-protection-system
  field
    chromiumRole : String
    aluminumRole : String
    scaleCompetition : String
    caveat : String
    sourceReference : String

open OxidationProtectionSystem public

canonicalOxidationProtectionSystem : OxidationProtectionSystem
canonicalOxidationProtectionSystem = oxidation-protection-system
  "Cr can support protective Cr2O3/chromia-forming behaviour and hot-corrosion resistance"
  "Al can support protective Al2O3/alumina-forming behaviour"
  "which scale is protective depends on composition, oxygen activity, temperature, exposure time and competing phases"
  "more Cr or Al is not definitionally better: excessive additions can alter phase stability, fabricability and mechanical properties"
  "high-temperature oxidation literature for Ni-base superalloys"

record ProcessingMicrostructurePropertyChain : Set where
  constructor processing-microstructure-property-chain
  field
    composition : String
    meltingAndRefining : String
    thermoMechanicalHistory : String
    heatTreatment : String
    realisedMicrostructure : String
    measuredProperties : String

open ProcessingMicrostructurePropertyChain public

canonicalProcessingChain : ProcessingMicrostructurePropertyChain
canonicalProcessingChain = processing-microstructure-property-chain
  "nominal alloy chemistry"
  "melt/refine/remelt route affects cleanliness and segregation state"
  "working and cooling history affect grain structure and stored deformation"
  "solutioning/ageing set precipitate state and may alter grain-boundary phases"
  "gamma/gamma-prime fraction, precipitate size/distribution, grain size, carbides/secondary phases, oxide-scale state"
  "tensile/creep/fatigue/oxidation/burn or ignition response under a specified protocol"

record SuperalloyBoundary : Set where
  constructor superalloy-boundary
  field
    sameCompositionMeansSameMicrostructure : Bool
    sameCompositionMeansSameMicrostructureIsFalse : sameCompositionMeansSameMicrostructure ≡ false
    gammaPrimePresentMeansOptimalStrength : Bool
    gammaPrimePresentMeansOptimalStrengthIsFalse : gammaPrimePresentMeansOptimalStrength ≡ false
    oxidationResistanceMeansBurnResistance : Bool
    oxidationResistanceMeansBurnResistanceIsFalse : oxidationResistanceMeansBurnResistance ≡ false
    higherStrengthMeansHigherBurnResistance : Bool
    higherStrengthMeansHigherBurnResistanceIsFalse : higherStrengthMeansHigherBurnResistance ≡ false
    publicCompositionDeterminesTacitProcess : Bool
    publicCompositionDeterminesTacitProcessIsFalse : publicCompositionDeterminesTacitProcess ≡ false

canonicalSuperalloyBoundary : SuperalloyBoundary
canonicalSuperalloyBoundary = superalloy-boundary
  false refl
  false refl
  false refl
  false refl
  false refl

data SuperalloyReverseTarget : Set where
  needExactHeatTreatment
  needGammaPrimeFractionAndSize
  needGrainAndSecondaryPhaseState
  needOxideScaleCharacterisation
  needMechanicalTestProtocol
  needBurnOrIgnitionProtocol
  needProcessingHistory
  : SuperalloyReverseTarget
