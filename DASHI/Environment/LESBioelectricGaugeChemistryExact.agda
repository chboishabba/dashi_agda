module DASHI.Environment.LESBioelectricGaugeChemistryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Biology.Levin.BioelectricChemistryWaveAdapter as Bioelectric
import DASHI.Chemistry.ExistingContentBridge as ChemistryReuse
import DASHI.Chemistry.TransitionKernel as Chemistry
import DASHI.Geometry.Gauge.SUNPrimitives as SUN
import DASHI.Physics.Units.SI as SI

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

yangMillsGaugeOwner : String
yangMillsGaugeOwner = "DASHI.Geometry.Gauge.SUNPrimitives"

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
    bioelectricMechanismNeedsFieldChemistryMembraneWeld : Bool
    bioelectricMechanismNeedsFieldChemistryMembraneWeldIsTrue : bioelectricMechanismNeedsFieldChemistryMembraneWeld ≡ true

canonicalLESBioelectricGaugeBoundary : LESBioelectricGaugeBoundary
canonicalLESBioelectricGaugeBoundary =
  lesBioelectricGaugeBoundary false refl false refl false refl false refl false refl true refl true refl
