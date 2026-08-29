module DASHI.Environment.LESBioelectricGaugeChemistryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Biology.Levin.BioelectricChemistryWaveAdapter as Bioelectric
import DASHI.Chemistry.ExistingContentBridge as ChemistryReuse
import DASHI.Chemistry.TransitionKernel as Chemistry
import DASHI.Geometry.Gauge.SUNPrimitives as SUN
import DASHI.Physics.Units.SI as SI
import DASHI.Physics.Electromagnetism.U1ElectromagneticApplicationExact as EM
import DASHI.Physics.Electromagnetism.PoissonNernstPlanckElectrodiffusionExact as PNP

------------------------------------------------------------------------
-- LES BIOELECTRIC / GAUGE / CHEMISTRY CROSS-POLLINATION
------------------------------------------------------------------------

data GaugeSector : Set where
  abelianElectromagneticSector
  nonAbelianYangMillsSector
  : GaugeSector

record ElectrochemicalFieldSocket : Set₁ where
  constructor electrochemicalFieldSocket
  field
    FieldState : Set
    MembraneState : Set
    ConcentrationState : Set

    voltageScale : SI.DecimalScale
    currentScale : SI.DecimalScale
    chargeScale : SI.DecimalScale
    concentrationScale : SI.DecimalScale
    electricFieldScale : SI.DecimalScale
    diffusionScale : SI.DecimalScale

    potentialFromField : FieldState → SI.Quantity SI.Voltage voltageScale
    ionicCurrent : MembraneState → ConcentrationState → SI.Quantity SI.Current currentScale
    chargeCarrier : ConcentrationState → SI.Quantity SI.Charge chargeScale
    amountConcentration : ConcentrationState → SI.Quantity SI.MolarConcentration concentrationScale
    electricField : FieldState → SI.Quantity SI.ElectricField electricFieldScale

    electromagneticLawReference : String
    electrochemicalPotentialReference : String
    membraneTransportReference : String
    geometryBoundaryReference : String

open ElectrochemicalFieldSocket public

record BioelectricChemistryWeld : Set₁ where
  constructor bioelectricChemistryWeld
  field
    bioelectricCarrier : Bioelectric.BioelectricChemistryWaveAdapter
    chemistryCarrier : ChemistryReuse.ExistingChemistryBridge
    fieldSocket : ElectrochemicalFieldSocket
    ionicSpeciesReference : String
    membranePotentialReference : String
    nernstOrElectrochemicalReference : String
    diffusionMigrationReference : String
    metabolicSupplyReference : String
    experimentalValidationReference : String

open BioelectricChemistryWeld public

record ElectrochemicalTransitionWeld
    (socket : ElectrochemicalFieldSocket) : Set₁ where
  constructor electrochemicalTransitionWeld
  field
    chemicalTransition : Chemistry.Transition
    diffusionCoefficient : SI.Quantity SI.DiffusionCoefficient (diffusionScale socket)
    fieldStateCouplingReference : String
    chargeConservationReference : String
    concentrationFluxReference : String
    interfacePermeabilityReference : String
    timeEvolutionReference : String

open ElectrochemicalTransitionWeld public

------------------------------------------------------------------------
-- Stronger cross-pollination: the bioelectric application can now consume the
-- independent U(1) and PNP owners directly. This closes the architecture gap
-- between a generic "membrane potential is relevant" carrier and a typed
-- electrodiffusion mechanism, while still requiring application validation.
------------------------------------------------------------------------

record BioelectricElectrodiffusionWeld : Set₁ where
  constructor bioelectricElectrodiffusionWeld
  field
    bioelectricChemistry : BioelectricChemistryWeld
    u1Reduction : EM.U1ApplicationReduction
    pnpApplication : PNP.ElectrodiffusionApplicationReceipt
    membranePotentialIdentificationReference : String
    ionicSpeciesIdentificationReference : String
    membraneInterfaceIdentificationReference : String
    neuralOrCellularValidationReference : String

open BioelectricElectrodiffusionWeld public

yangMillsGaugeOwner : String
yangMillsGaugeOwner = "DASHI.Geometry.Gauge.SUNPrimitives"

u1ElectromagneticOwner : String
u1ElectromagneticOwner =
  "DASHI.Physics.Electromagnetism.U1ElectromagneticApplicationExact"

pnpElectrodiffusionOwner : String
pnpElectrodiffusionOwner =
  "DASHI.Physics.Electromagnetism.PoissonNernstPlanckElectrodiffusionExact; DOI 10.3390/electrochem2020014"

siQuantityOwner : String
siQuantityOwner = "DASHI.Physics.Units.SI; BIPM DOI 10.59161/AUEZ1291"

yangMillsPromotionImported : Bool
yangMillsPromotionImported = SUN.clayYangMillsPromoted

yangMillsPromotionImportedIsFalse : yangMillsPromotionImported ≡ false
yangMillsPromotionImportedIsFalse = SUN.clayYangMillsPromotedIsFalse

record LESBioelectricGaugeBoundary : Set where
  constructor lesBioelectricGaugeBoundary
  field
    bioelectricityIsNonAbelianYangMills : Bool
    bioelectricityIsNonAbelianYangMillsIsFalse : bioelectricityIsNonAbelianYangMills ≡ false
    suNGaugeOwnerProvesU1Electromagnetism : Bool
    suNGaugeOwnerProvesU1ElectromagnetismIsFalse : suNGaugeOwnerProvesU1Electromagnetism ≡ false
    membranePotentialBoolIsQuantitativeVoltage : Bool
    membranePotentialBoolIsQuantitativeVoltageIsFalse : membranePotentialBoolIsQuantitativeVoltage ≡ false
    chemistryChargeLabelIsDimensionedChargeQuantity : Bool
    chemistryChargeLabelIsDimensionedChargeQuantityIsFalse : chemistryChargeLabelIsDimensionedChargeQuantity ≡ false
    nernstSurfaceAloneIsCellularElectrodynamics : Bool
    nernstSurfaceAloneIsCellularElectrodynamicsIsFalse : nernstSurfaceAloneIsCellularElectrodynamics ≡ false
    electrochemicalSocketUsesCanonicalSIQuantities : Bool
    electrochemicalSocketUsesCanonicalSIQuantitiesIsTrue : electrochemicalSocketUsesCanonicalSIQuantities ≡ true
    independentU1OwnerNowReferenced : Bool
    independentU1OwnerNowReferencedIsTrue : independentU1OwnerNowReferenced ≡ true
    pnpElectrodiffusionOwnerNowReferenced : Bool
    pnpElectrodiffusionOwnerNowReferencedIsTrue : pnpElectrodiffusionOwnerNowReferenced ≡ true
    bioelectricMechanismNeedsApplicationValidation : Bool
    bioelectricMechanismNeedsApplicationValidationIsTrue : bioelectricMechanismNeedsApplicationValidation ≡ true

canonicalLESBioelectricGaugeBoundary : LESBioelectricGaugeBoundary
canonicalLESBioelectricGaugeBoundary =
  lesBioelectricGaugeBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
    true refl
    true refl
    true refl
