module DASHI.Environment.LESBioelectricGaugeChemistryExact where

open import DASHI.Core.Prelude

import DASHI.Biology.Levin.BioelectricChemistryWaveAdapter as Bioelectric
import DASHI.Chemistry.ExistingContentBridge as ChemistryReuse
import DASHI.Chemistry.TransitionKernel as Chemistry
import DASHI.Geometry.Gauge.SUNPrimitives as SUN

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
-- electrochemical law surface, unit discipline, membrane geometry and
-- experiment receipts.  The YM lane is evidence that gauge structure is an
-- established repository concept, not authority for a U(1) biological model.
------------------------------------------------------------------------

data GaugeSector : Set where
  abelianElectromagneticSector
  nonAbelianYangMillsSector
  : GaugeSector

record ElectrochemicalFieldSocket : Set₁ where
  constructor electrochemicalFieldSocket
  field
    Charge : Set
    Potential : Set
    Current : Set
    Concentration : Set
    FieldState : Set
    MembraneState : Set

    potentialFromField : FieldState → Potential
    ionicCurrent : MembraneState → Concentration → Current
    chargeCarrier : Concentration → Charge

    unitSystemReference : String
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

    chargeLabelIsDimensionedChargeQuantity : Bool
    chargeLabelIsDimensionedChargeQuantityIsFalse :
      chargeLabelIsDimensionedChargeQuantity ≡ false

    nernstSurfaceAloneIsCellularElectrodynamics : Bool
    nernstSurfaceAloneIsCellularElectrodynamicsIsFalse :
      nernstSurfaceAloneIsCellularElectrodynamics ≡ false

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
