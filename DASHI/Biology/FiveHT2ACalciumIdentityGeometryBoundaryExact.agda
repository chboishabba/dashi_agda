module DASHI.Biology.FiveHT2ACalciumIdentityGeometryBoundaryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Biology.FiveHT2AVisualCortexBioelectricBridgeExact as V1
import DASHI.Biology.IonicMimicryGeometryExact as Mimicry
import DASHI.Biology.NeurochemicalAtomicChemistryBridge as AtomicChem
import DASHI.Biology.Cell.BioelectricNetwork as Bioelectric

------------------------------------------------------------------------
-- CALCIUM IS NOT A SCALAR
--
-- The 5-HT2A/V1 lane currently carries a calcium readout coordinate.
-- Pb2+/Ca2+ ionic mimicry demonstrates why that coordinate must not collapse
-- to "amount of calcium":
--
--   species identity
--   x concentration
--   x compartment/location
--   x binding target
--   x coordination geometry / hydration
--   x protein conformational response
--   x time/protocol.
--
-- Pb2+ is NOT proposed as part of the psychedelic mechanism.  It is consumed
-- as a counterexample/calibration fixture against scalarizing calcium biology.
------------------------------------------------------------------------

data CalciumStateCoordinate : Set where
  ionIdentityCoordinate : CalciumStateCoordinate
  concentrationCoordinate : CalciumStateCoordinate
  compartmentCoordinate : CalciumStateCoordinate
  targetProteinCoordinate : CalciumStateCoordinate
  bindingSiteCoordinate : CalciumStateCoordinate
  coordinationGeometryCoordinate : CalciumStateCoordinate
  hydrationCoordinate : CalciumStateCoordinate
  conformationalResponseCoordinate : CalciumStateCoordinate
  temporalCoordinate : CalciumStateCoordinate
  protocolCoordinate : CalciumStateCoordinate

canonicalCalciumStateCoordinates : List CalciumStateCoordinate
canonicalCalciumStateCoordinates =
  ionIdentityCoordinate
  ∷ concentrationCoordinate
  ∷ compartmentCoordinate
  ∷ targetProteinCoordinate
  ∷ bindingSiteCoordinate
  ∷ coordinationGeometryCoordinate
  ∷ hydrationCoordinate
  ∷ conformationalResponseCoordinate
  ∷ temporalCoordinate
  ∷ protocolCoordinate
  ∷ []

data CalciumStateMeaning : Set where
  freeCytosolicCalciumCandidate : CalciumStateMeaning
  boundProteinCalciumCandidate : CalciumStateMeaning
  storeReleaseCandidate : CalciumStateMeaning
  membraneFluxCandidate : CalciumStateMeaning
  reporterSignalCandidate : CalciumStateMeaning
  calciumLikeMimicCandidate : CalciumStateMeaning

record CalciumReadoutRefinement : Set where
  constructor calciumReadoutRefinement
  field
    originalV1Readout : V1.CircuitReadoutKind
    coordinates : List CalciumStateCoordinate
    meaning : CalciumStateMeaning
    protocolReference : String

    readoutIsNotIonIdentityByDefinition : Bool
    readoutIsNotIonIdentityByDefinitionIsTrue :
      readoutIsNotIonIdentityByDefinition ≡ true

    fluorescenceOrReporterIsNotFreeCalciumByDefinition : Bool
    fluorescenceOrReporterIsNotFreeCalciumByDefinitionIsTrue :
      fluorescenceOrReporterIsNotFreeCalciumByDefinition ≡ true

open CalciumReadoutRefinement public

canonicalFiveHT2ACalciumReadoutRefinement : CalciumReadoutRefinement
canonicalFiveHT2ACalciumReadoutRefinement =
  calciumReadoutRefinement
    V1.calciumReadout
    canonicalCalciumStateCoordinates
    reporterSignalCandidate
    "source/protocol indexed calcium readout"
    true refl
    true refl

------------------------------------------------------------------------
-- Pb2+ fixture: an adversarial example for scalar calcium semantics.
------------------------------------------------------------------------

record CalciumMimicryCounterexample : Set where
  constructor calciumMimicryCounterexample
  field
    nativeIon : Mimicry.IonIdentity
    mimicIon : Mimicry.IonIdentity
    mimicryBoundary : Mimicry.IonicMimicryGeometryBoundary
    targetRelativeFixture : Mimicry.TargetRelativeMimicry

    sameFormalCharge : Bool
    sameFormalChargeIsTrue :
      sameFormalCharge ≡ true

    sameChemicalIdentity : Bool
    sameChemicalIdentityIsFalse :
      sameChemicalIdentity ≡ false

    substitutionPossibleInSomeTargets : Bool
    substitutionPossibleInSomeTargetsIsTrue :
      substitutionPossibleInSomeTargets ≡ true

    substitutionOutcomeTargetDependent : Bool
    substitutionOutcomeTargetDependentIsTrue :
      substitutionOutcomeTargetDependent ≡ true

open CalciumMimicryCounterexample public

canonicalPbCalciumMimicryCounterexample : CalciumMimicryCounterexample
canonicalPbCalciumMimicryCounterexample =
  calciumMimicryCounterexample
    Mimicry.calciumII
    Mimicry.leadII
    Mimicry.canonicalIonicMimicryGeometryBoundary
    Mimicry.canonicalPbCaTargetRelativeMimicry
    true refl
    false refl
    true refl
    true refl

------------------------------------------------------------------------
-- Existing atomic-chemistry lane is retained.
------------------------------------------------------------------------

atomicChemistrySlots : List AtomicChem.NeurochemicalAtomicChemistrySlot
atomicChemistrySlots =
  AtomicChem.canonicalNeurochemicalAtomicChemistrySlots

relevantAtomicChemistryReading : String
relevantAtomicChemistryReading =
  "The existing atomic chemistry slots already separate formula/species identity, charge, protonation, conformer, binding and kinetics. Calcium signaling therefore cannot be represented faithfully by a bare scalar concentration coordinate."

------------------------------------------------------------------------
-- Bioelectric consequence: chemical identity and electrical state are
-- different fibres.
------------------------------------------------------------------------

record CalciumBioelectricSeparation : Set where
  constructor calciumBioelectricSeparation
  field
    bioelectricOwner : Bioelectric.BioelectricNetwork
    calciumReadout : CalciumReadoutRefinement
    mimicryCounterexample : CalciumMimicryCounterexample

    chemicalSpeciesIsVoltage : Bool
    chemicalSpeciesIsVoltageIsFalse :
      chemicalSpeciesIsVoltage ≡ false

    reporterSignalIsIonicCurrent : Bool
    reporterSignalIsIonicCurrentIsFalse :
      reporterSignalIsIonicCurrent ≡ false

    ionBindingGeometryDeterminesNetworkState : Bool
    ionBindingGeometryDeterminesNetworkStateIsFalse :
      ionBindingGeometryDeterminesNetworkState ≡ false

open CalciumBioelectricSeparation public

canonicalCalciumBioelectricSeparation : CalciumBioelectricSeparation
canonicalCalciumBioelectricSeparation =
  calciumBioelectricSeparation
    V1.abstractBioelectricNetwork
    canonicalFiveHT2ACalciumReadoutRefinement
    canonicalPbCalciumMimicryCounterexample
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Anti-collapse.
------------------------------------------------------------------------

data CalciumSignalIsJustConcentration : Set where
data SameChargeImpliesSameCalciumSignal : Set where
data LeadMimicryIsPartOfPsychedelicMechanism : Set where
data ReporterIntensityDeterminesBindingGeometry : Set where

calciumSignalIsNotJustConcentration :
  CalciumSignalIsJustConcentration → ⊥
calciumSignalIsNotJustConcentration ()

sameChargeDoesNotImplySameCalciumSignal :
  SameChargeImpliesSameCalciumSignal → ⊥
sameChargeDoesNotImplySameCalciumSignal ()

leadMimicryIsNotPsychedelicMechanism :
  LeadMimicryIsPartOfPsychedelicMechanism → ⊥
leadMimicryIsNotPsychedelicMechanism ()

reporterIntensityDoesNotDetermineBindingGeometry :
  ReporterIntensityDeterminesBindingGeometry → ⊥
reporterIntensityDoesNotDetermineBindingGeometry ()

------------------------------------------------------------------------
-- Frontier.
------------------------------------------------------------------------

record CalciumGeometryFrontier : Set where
  constructor calciumGeometryFrontier
  field
    currentCorrection : String
    requiredMeasurement : String
    requiredMolecularJoin : String
    requiredElectricalJoin : String

canonicalCalciumGeometryFrontier : CalciumGeometryFrontier
canonicalCalciumGeometryFrontier =
  calciumGeometryFrontier
    "refine calciumReadout from a scalar-like label into species x compartment x target x coordination geometry x conformation x time/protocol"
    "same-protocol calibrated free/bound Ca2+ measurement with cell type, compartment and temporal resolution"
    "identify the relevant Ca2+-binding proteins/channels downstream of the 5-HT2A perturbation and preserve their target-specific coordination state"
    "join chemical/calcium state to membrane voltage/current/channel state only with direct electrophysiology or validated mechanistic calibration"
