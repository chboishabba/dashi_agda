module DASHI.Geology.SaltGeochemistryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Chemistry.TransitionKernel as Chemistry
import DASHI.Physics.Electromagnetism.PoissonNernstPlanckElectrodiffusionExact as PNP

------------------------------------------------------------------------
-- SALT GEOCHEMISTRY: HALITE -> BRINE -> IONIC TRANSPORT
--
-- This module establishes the first literal geology/mineral carrier in DASHI.
-- It is intentionally narrow.  It does not claim a universal sedimentary,
-- basin-evolution, weathering or groundwater model.
--
-- Scientific source anchors:
--   Warren, J. K. (2006), Evaporites: Sediments, Resources and Hydrocarbons.
--   Drever, J. I. (1997), The Geochemistry of Natural Waters, 3rd ed.
--
-- Repository reuse:
--   * DASHI.Chemistry.TransitionKernel owns species, phase, charge,
--     composition, reactions, compartments, ionic strength and conservation.
--   * DASHI.Physics.Electromagnetism.PoissonNernstPlanckElectrodiffusionExact
--     owns valence-typed concentration/diffusion/flux electrodiffusion.
------------------------------------------------------------------------

data SaltReservoirKind : Set where
  evaporiteBed
  saltDome
  brineAquifer
  surfaceBrine
  seawaterReservoir
  industrialBrineReservoir
  : SaltReservoirKind

data SaltGeochemicalProcess : Set where
  haliteDissolution
  halitePrecipitation
  evaporativeConcentration
  aqueousDilution
  advectiveSaltTransport
  diffusiveSaltTransport
  : SaltGeochemicalProcess

------------------------------------------------------------------------
-- Canonical chemistry species used by the salt spine.
------------------------------------------------------------------------

haliteSpecies : Chemistry.Species
haliteSpecies = record
  { Chemistry.speciesId = "halite / sodium chloride mineral"
  ; Chemistry.phase = Chemistry.solid
  ; Chemistry.chargeLabel = "electrically neutral formula unit"
  ; Chemistry.compositionLabel = "NaCl"
  ; Chemistry.mobilityClass = Chemistry.immobile
  ; Chemistry.activityModelLabel = "solid halite activity / geochemical model supplied by application"
  ; Chemistry.opticalRoleLabel = "not asserted"
  ; Chemistry.evidence = Chemistry.literatureEstablished
  }

sodiumIonSpecies : Chemistry.Species
sodiumIonSpecies = record
  { Chemistry.speciesId = "sodium ion"
  ; Chemistry.phase = Chemistry.dissolved
  ; Chemistry.chargeLabel = "+1"
  ; Chemistry.compositionLabel = "Na+"
  ; Chemistry.mobilityClass = Chemistry.mobile
  ; Chemistry.activityModelLabel = "aqueous electrolyte activity model supplied by application"
  ; Chemistry.opticalRoleLabel = "not asserted"
  ; Chemistry.evidence = Chemistry.literatureEstablished
  }

chlorideIonSpecies : Chemistry.Species
chlorideIonSpecies = record
  { Chemistry.speciesId = "chloride ion"
  ; Chemistry.phase = Chemistry.dissolved
  ; Chemistry.chargeLabel = "-1"
  ; Chemistry.compositionLabel = "Cl-"
  ; Chemistry.mobilityClass = Chemistry.mobile
  ; Chemistry.activityModelLabel = "aqueous electrolyte activity model supplied by application"
  ; Chemistry.opticalRoleLabel = "not asserted"
  ; Chemistry.evidence = Chemistry.literatureEstablished
  }

haliteIsSolid : Chemistry.phase haliteSpecies ≡ Chemistry.solid
haliteIsSolid = refl

sodiumIsDissolved : Chemistry.phase sodiumIonSpecies ≡ Chemistry.dissolved
sodiumIsDissolved = refl

chlorideIsDissolved : Chemistry.phase chlorideIonSpecies ≡ Chemistry.dissolved
chlorideIsDissolved = refl

------------------------------------------------------------------------
-- Geological reservoir and phase-change ownership.
------------------------------------------------------------------------

record SaltReservoir : Set where
  constructor saltReservoir
  field
    reservoirId : String
    reservoirKind : SaltReservoirKind
    geometryReference : String
    hostLithologyReference : String
    fluidOrPoreSpaceReference : String
    salinityOrHaliteInventoryReference : String
    temperaturePressureReference : String
    provenanceReference : String

open SaltReservoir public

record HaliteBrinePhaseWeld : Set where
  constructor haliteBrinePhaseWeld
  field
    solidHalite : Chemistry.Species
    aqueousSodium : Chemistry.Species
    aqueousChloride : Chemistry.Species

    solidHaliteIsCanonical : solidHalite ≡ haliteSpecies
    aqueousSodiumIsCanonical : aqueousSodium ≡ sodiumIonSpecies
    aqueousChlorideIsCanonical : aqueousChloride ≡ chlorideIonSpecies

    dissolutionTransition : Chemistry.Transition
    precipitationTransition : Chemistry.Transition

    dissolutionStoichiometryReference : String
    precipitationStoichiometryReference : String
    solubilityActivityReference : String
    temperaturePressureValidityReference : String
    massBalanceReference : String
    chargeBalanceReference : String

open HaliteBrinePhaseWeld public

------------------------------------------------------------------------
-- Brine is not identified with a single NaCl species.  It is a compartmental
-- aqueous state containing literal dissolved ionic species plus an externally
-- supplied composition/activity model.
------------------------------------------------------------------------

record BrineState : Set where
  constructor brineState
  field
    reservoir : SaltReservoir
    aqueousCompartment : Chemistry.Compartment
    sodiumSpecies : Chemistry.Species
    chlorideSpecies : Chemistry.Species
    sodiumIsCanonical : sodiumSpecies ≡ sodiumIonSpecies
    chlorideIsCanonical : chlorideSpecies ≡ chlorideIonSpecies
    ionicStrengthReference : String
    waterActivityReference : String
    majorMinorIonCompositionReference : String
    electroneutralityReference : String
    salinityMeasurementReference : String

open BrineState public

------------------------------------------------------------------------
-- Same-species bridge into the existing PNP electrodiffusion carrier.
-- The carriers are intentionally not equated by type: Chemistry.Species stores
-- chemical identity metadata, whereas PNP.IonicSpeciesState stores a dynamic
-- valence/concentration/diffusion state.  A weld must explicitly identify them.
------------------------------------------------------------------------

record ChemistryPNPIonWeld : Set₁ where
  constructor chemistryPNPIonWeld
  field
    chemistrySpecies : Chemistry.Species
    dynamicSpecies : PNP.IonicSpeciesState
    chemicalIdentityReference : String
    valenceAgreementReference : String
    concentrationSpeciesReference : String
    activityConcentrationCompatibilityReference : String
    commonSpaceTimeReference : String
    validationReference : String

open ChemistryPNPIonWeld public

record BrineElectrodiffusionWeld (brine : BrineState) : Set₁ where
  constructor brineElectrodiffusionWeld
  field
    sodiumWeld : ChemistryPNPIonWeld
    chlorideWeld : ChemistryPNPIonWeld

    sodiumChemistryIdentity :
      chemistrySpecies sodiumWeld ≡ sodiumSpecies brine
    chlorideChemistryIdentity :
      chemistrySpecies chlorideWeld ≡ chlorideSpecies brine

    sodiumTransport : PNP.ElectrodiffusionApplicationReceipt
    chlorideTransport : PNP.ElectrodiffusionApplicationReceipt

    sodiumApplicationIsAqueous :
      PNP.application sodiumTransport ≡ PNP.aqueousEnvironmentalTransport
    chlorideApplicationIsAqueous :
      PNP.application chlorideTransport ≡ PNP.aqueousEnvironmentalTransport

    sodiumDynamicIdentity :
      PNP.species sodiumTransport ≡ dynamicSpecies sodiumWeld
    chlorideDynamicIdentity :
      PNP.species chlorideTransport ≡ dynamicSpecies chlorideWeld

    commonFluidStateReference : String
    commonElectrostaticStateReference : String
    coupledElectroneutralityReference : String
    transportValidationReference : String

open BrineElectrodiffusionWeld public

------------------------------------------------------------------------
-- Material-provenance chain.  This is the geological-to-chemical seam that a
-- downstream industrial or ecological consumer must preserve.
------------------------------------------------------------------------

record SaltMaterialLineage : Set₁ where
  constructor saltMaterialLineage
  field
    sourceReservoir : SaltReservoir
    phaseWeld : HaliteBrinePhaseWeld
    brine : BrineState
    ionTransport : BrineElectrodiffusionWeld brine

    haliteToBrineProvenanceReference : String
    sodiumAtomContinuityReference : String
    chlorineAtomContinuityReference : String
    extractionOrNaturalMobilisationReference : String
    commonMaterialLedgerReference : String

open SaltMaterialLineage public

------------------------------------------------------------------------
-- Authority boundary.
------------------------------------------------------------------------

record SaltGeochemistryBoundary : Set where
  constructor saltGeochemistryBoundary
  field
    haliteSpeciesAloneIsGeologicalDepositModel : Bool
    haliteSpeciesAloneIsGeologicalDepositModelIsFalse :
      haliteSpeciesAloneIsGeologicalDepositModel ≡ false

    brineIsPureNaClSolution : Bool
    brineIsPureNaClSolutionIsFalse : brineIsPureNaClSolution ≡ false

    salinityScalarDeterminesFullIonicComposition : Bool
    salinityScalarDeterminesFullIonicCompositionIsFalse :
      salinityScalarDeterminesFullIonicComposition ≡ false

    chemistrySpeciesEqualsPNPDynamicStateByType : Bool
    chemistrySpeciesEqualsPNPDynamicStateByTypeIsFalse :
      chemistrySpeciesEqualsPNPDynamicStateByType ≡ false

    oneSolubilityModelValidForAllNaturalBrines : Bool
    oneSolubilityModelValidForAllNaturalBrinesIsFalse :
      oneSolubilityModelValidForAllNaturalBrines ≡ false

    materialLineageNeedsProvenanceAndValidation : Bool
    materialLineageNeedsProvenanceAndValidationIsTrue :
      materialLineageNeedsProvenanceAndValidation ≡ true

canonicalSaltGeochemistryBoundary : SaltGeochemistryBoundary
canonicalSaltGeochemistryBoundary =
  saltGeochemistryBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
