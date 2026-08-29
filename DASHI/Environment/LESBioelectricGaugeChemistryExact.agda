module DASHI.Environment.LESBioelectricGaugeChemistryExact where

open import DASHI.Core.Prelude

import DASHI.Biology.Levin.BioelectricChemistryWaveAdapter as Bioelectric
import DASHI.Chemistry.ExistingContentBridge as ChemistryReuse
import DASHI.Chemistry.TransitionKernel as Chemistry
import DASHI.Geometry.Gauge.SUNPrimitives as SUN
import DASHI.Physics.SIQuantitiesExact as SI

------------------------------------------------------------------------
-- LES BIOELECTRIC / GAUGE / CHEMISTRY CROSS-POLLINATION
--
-- Repository-native architecture owner.
--
-- The Levin lane already records ionic composition, membrane potential,
-- hydration/phase, metabolic energy and geometry as relevant physical
-- chemistry coordinates.  Chemistry already records species, charge labels,
-- Nernst-compatible quantitative-law surfaces and transition structure.  The
-- Yang-Mills tree owns a non-abelian SU(N) gauge lane.
--
-- The correct reuse boundary is NOT "bioelectricity = Yang-Mills".  A real
-- bioelectric application needs an independently supplied electromagnetic /
-- electrochemical law surface, SI dimension discipline, membrane geometry and
-- experiment receipts.  The YM lane is evidence that gauge structure is an
-- established repository concept, not authority for a U(1) biological model.
------------------------------------------------------------------------

data GaugeSector : Set where
  abelianElectromagneticSector
  nonAbelianYangMillsSector
  : GaugeSector

------------------------------------------------------------------------
-- Quantitative electrochemical socket.
--
-- Scalar remains application-selectable (exact rational, interval, measured
-- value with uncertainty, etc.), while electrical and concentration quantities
-- are dimension-indexed by the BIPM-calibrated SI owner.
------------------------------------------------------------------------

record ElectrochemicalFieldSocket : Set₁ where
  constructor electrochemicalFieldSocket
  field
    Scalar : Set
    FieldState : Set
    MembraneState : Set
    ConcentrationState : Set

    potentialFromField : FieldState → SI.Voltage Scalar
    ionicCurrent : MembraneState → ConcentrationState → SI.Current Scalar
    chargeCarrier : ConcentrationState → SI.Charge Scalar
    amountConcentration : ConcentrationState → SI.Concentration Scalar
    electricField : FieldState → SI.ElectricField Scalar

    siQuantityOwnerReference : String
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

------------------------------------------------------------------------
-- A stronger application can explicitly combine a chemistry transition with a
-- bioelectric field socket.  This records the exact coupling seam without
-- pretending the generic chemistry transition kernel has electrodiffusion
-- semantics by definition.
------------------------------------------------------------------------

record ElectrochemicalTransitionWeld
    (socket : ElectrochemicalFieldSocket) : Set₁ where
  constructor electrochemicalTransitionWeld
  field
    chemicalTransition : Chemistry.Transition
    diffusionCoefficient : SI.DiffusionCoefficient (Scalar socket)
    fieldStateCouplingReference : String
    chargeConservationReference : String
    concentrationFluxReference : String
    interfacePermeabilityReference : String
    timeEvolutionReference : String

open ElectrochemicalTransitionWeld public

------------------------------------------------------------------------
-- Explicit YM provenance boundary.
------------------------------------------------------------------------

yangMillsGaugeOwner : String
yangMillsGaugeOwner = "DASHI.Geometry.Gauge.SUNPrimitives"

siQuantityOwner : String
siQuantityOwner = "DASHI.Physics.SIQuantitiesExact; BIPM DOI 10.59161/AUEZ1291"

yangMillsPromotionImported : Bool
yangMillsPromotionImported = SUN.clayYangMillsPromoted

yangMillsPromotionImportedIsFalse : yangMillsPromotionImported ≡ false
yangMillsPromotionImportedIsFalse = SUN.clayYangMillsPromotedIsFalse

record LESBioelectricGaugeBoundary : Set where
  constructor lesBioelectricGaugeBoundary
  field
    bioelectricityIsNonAbelianYangMills : Bool
    bioelectricityIsNonAbelianYangMillsIsFalse :
      bioelectricityIsNonAbelianYangMills ≡ false

    suNGaugeOwnerProvesU1Electromagnetism : Bool
    suNGaugeOwnerProvesU1ElectromagnetismIsFalse :
      suNGaugeOwnerProvesU1Electromagnetism ≡ false

    membranePotentialBoolIsQuantitativeVoltage : Bool
    membranePotentialBoolIsQuantitativeVoltageIsFalse :
      membranePotentialBoolIsQuantitativeVoltage ≡ false

    chemistryChargeLabelIsDimensionedChargeQuantity : Bool
    chemistryChargeLabelIsDimensionedChargeQuantityIsFalse :
      chemistryChargeLabelIsDimensionedChargeQuantity ≡ false

    nernstSurfaceAloneIsCellularElectrodynamics : Bool
    nernstSurfaceAloneIsCellularElectrodynamicsIsFalse :
      nernstSurfaceAloneIsCellularElectrodynamics ≡ false

    electrochemicalSocketUsesTypedSIQuantities : Bool
    electrochemicalSocketUsesTypedSIQuantitiesIsTrue :
      electrochemicalSocketUsesTypedSIQuantities ≡ true

    bioelectricMechanismNeedsFieldChemistryMembraneWeld : Bool
    bioelectricMechanismNeedsFieldChemistryMembraneWeldIsTrue :
      bioelectricMechanismNeedsFieldChemistryMembraneWeld ≡ true

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
