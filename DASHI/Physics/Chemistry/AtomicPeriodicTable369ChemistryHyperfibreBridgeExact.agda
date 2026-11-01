module DASHI.Physics.Chemistry.AtomicPeriodicTable369ChemistryHyperfibreBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Chemistry.AtomicPeriodicTable369GenerativeExact as Atomic369
import DASHI.Physics.Chemistry.AtomicPeriodicTable369PhysicalValidation as Physical
import DASHI.Physics.Foundations.AtomicValenceFermionBridgeExact as AtomicValence
import DASHI.Biology.Molecular.MolecularAssemblyBoundary as Molecular
import DASHI.Chemistry.TransitionKernel as Chemistry
import DASHI.Chemistry.AdmissibleReactionTransitionBridgeExact as Reaction
import DASHI.Chemistry.SaltPetroleumIndustrialChemistryNetworkExact as Industrial
import DASHI.Chemistry.CarbonChemicalSuitabilityLifeBoundaryExact as Carbon
import DASHI.Chemistry.AlliumMolecularTrajectoryExact as Allium

------------------------------------------------------------------------
-- ATOMIC -> MOLECULAR -> REACTION -> INDUSTRIAL CHEMISTRY HYPERFIBRE
--
-- Thin cross-pollination owner.  It does not add a competing chemistry
-- ontology: it composes the existing atomic/valence, molecular assembly,
-- admissible-reaction, industrial material-lineage and time-indexed molecular
-- trajectory owners into one fibre-over-time contract.
--
-- The central discipline is that each downstream level consumes an upstream
-- witness but introduces genuinely new proof obligations:
--
-- atomic state
--   -> valence / one-particle / fermionic information
--   -> molecular identity + bond/geometry/stereo/environment
--   -> reaction enablement + conservation + kinetics context
--   -> process/material lineage + separation/safety/quality
--   -> observed product/plant state.
--
-- None of those arrows is an equality or automatic promotion.
------------------------------------------------------------------------

record ChemistryHyperfibreSystem : Set₁ where
  constructor chemistryHyperfibreSystem
  field
    Time : Set

    AtomicStateAt : Time -> Set
    MolecularStateAt : Time -> Set
    ReactionStateAt : Time -> Set
    IndustrialStateAt : Time -> Set

    atomToMolecule :
      (t : Time) -> AtomicStateAt t -> MolecularStateAt t -> Set
    moleculeToReaction :
      (t : Time) -> MolecularStateAt t -> ReactionStateAt t -> Set
    reactionToIndustrial :
      (t : Time) -> ReactionStateAt t -> IndustrialStateAt t -> Set

    atomicSourceReference : (t : Time) -> String
    molecularSourceReference : (t : Time) -> String
    reactionSourceReference : (t : Time) -> String
    industrialSourceReference : (t : Time) -> String
    fibreVersionReference : (t : Time) -> String

open ChemistryHyperfibreSystem public

record ChemistryFibre
  (S : ChemistryHyperfibreSystem)
  (t : Time S) : Set₁ where
  constructor chemistryFibre
  field
    atomState : AtomicStateAt S t
    moleculeState : MolecularStateAt S t
    reactionState : ReactionStateAt S t
    industrialState : IndustrialStateAt S t

    atomMoleculeWeld : atomToMolecule S t atomState moleculeState
    moleculeReactionWeld : moleculeToReaction S t moleculeState reactionState
    reactionIndustrialWeld :
      reactionToIndustrial S t reactionState industrialState

    atomProvenance : String
    moleculeProvenance : String
    reactionProvenance : String
    industrialProvenance : String

open ChemistryFibre public

------------------------------------------------------------------------
-- Time transport is proof-relevant.  Equal nominal material/product labels do
-- not collapse the history fibre.  This is the same discipline already used by
-- the Allium trajectory and industrial custody/material-lineage owners.
------------------------------------------------------------------------

record ChemistryFibreTransport
  {S : ChemistryHyperfibreSystem}
  {t0 t1 : Time S}
  (source : ChemistryFibre S t0)
  (target : ChemistryFibre S t1) : Set where
  constructor chemistryFibreTransport
  field
    timePathReference : String
    atomicIdentityTransportReference : String
    molecularIdentityTransportReference : String
    reactionHistoryReference : String
    processHistoryReference : String
    sourceProvenancePreserved : Bool
    sourceProvenancePreservedIsTrue : sourceProvenancePreserved ≡ true
    appendOnlyHistoryPreserved : Bool
    appendOnlyHistoryPreservedIsTrue : appendOnlyHistoryPreserved ≡ true

------------------------------------------------------------------------
-- Existing-owner witnesses: these fields deliberately reuse repo-native
-- boundaries rather than restating their mathematics.
------------------------------------------------------------------------

atomicValenceBoundary : AtomicValence.AtomicValenceFermionBoundary
atomicValenceBoundary = AtomicValence.canonicalAtomicValenceFermionBoundary

carbonSuitabilityBoundary : Carbon.CarbonChemicalSuitabilityBoundary
carbonSuitabilityBoundary = Carbon.canonicalCarbonChemicalSuitabilityBoundary

industrialChemistryBoundary : Industrial.SaltPetroleumIndustrialChemistryBoundary
industrialChemistryBoundary = Industrial.canonicalSaltPetroleumIndustrialChemistryBoundary

alliumTrajectoryBoundary : Allium.MolecularTrajectoryBoundary
alliumTrajectoryBoundary = Allium.canonicalMolecularTrajectoryBoundary

------------------------------------------------------------------------
-- Application receipts.  The point is to make the extra obligations visible
-- at the transition from atoms to real chemistry.
------------------------------------------------------------------------

record AtomicToSpeciesReceipt : Set where
  constructor atomicToSpeciesReceipt
  field
    elementIdentityReference : String
    chargeStateReference : String
    isotopicStateReference : String
    valenceReference : String
    electronicStateReference : String
    speciesIdentityReference : String
    compositionReference : String
    sameObjectReference : String

record SpeciesToMoleculeReceipt : Set where
  constructor speciesToMoleculeReceipt
  field
    atomInventoryReference : String
    bondOrderReference : String
    geometryReference : String
    stereochemistryReference : String
    chargeBalanceReference : String
    environmentReference : String
    stabilityReference : String
    observationalIdentityReference : String

record MoleculeToReactionReceipt : Set where
  constructor moleculeToReactionReceipt
  field
    reactantIdentityReference : String
    productIdentityReference : String
    stoichiometryReference : String
    elementConservationReference : String
    chargeConservationReference : String
    enablementReference : String
    rateLawReference : String
    environmentReference : String
    measurementReference : String

record ReactionToIndustrialReceipt : Set where
  constructor reactionToIndustrialReceipt
  field
    processKindReference : String
    feedstockReference : String
    operatingEnvelopeReference : String
    separationReference : String
    safetyReference : String
    yieldSelectivityReference : String
    inventoryLotReference : String
    qualitySpecificationReference : String
    plantValidationReference : String

------------------------------------------------------------------------
-- Canonical cross-pollination coordinates from existing chemistry lanes.
------------------------------------------------------------------------

petrochemicalJoinReading : String
petrochemicalJoinReading =
  "SaltPetroleumIndustrialChemistryNetworkExact already treats chlor-alkali, steam cracking, chlorination, dehydrochlorination, polymerisation, hydrogenation and neutralisation as distinct process kinds; atomic/valence structure can constrain species identity but cannot replace feedstock, operating-envelope, separation, safety, yield or plant-validation receipts."

carbonJoinReading : String
carbonJoinReading =
  "CarbonChemicalSuitabilityLifeBoundaryExact already proves the required anti-collapse: valence class alone does not predict all chemistry. Atomic periodic-table recovery therefore supplies an upstream constraint, not a theorem of catenation, bond diversity, aqueous stability, redox range or molecular combinatorics."

alliumJoinReading : String
alliumJoinReading =
  "AlliumMolecularTrajectoryExact is the concrete time-indexed exemplar: identical starting ingredient labels need not determine the same matured composition, and source-backed transformation families do not establish the target preparation without time-resolved measurement."

reactionJoinReading : String
reactionJoinReading =
  "AdmissibleReactionTransitionBridgeExact separates hard reaction enablement from conditional kinetic weight. Atomic or molecular identity cannot be substituted for an enablement witness, and a string-valued rate/guard carrier is not quantitative chemistry."

------------------------------------------------------------------------
-- Non-promotion theorem surface.
------------------------------------------------------------------------

record AtomicChemistryCrossPollinationBoundary : Set where
  constructor atomicChemistryCrossPollinationBoundary
  field
    periodicTableRecoveryDeterminesMolecularIdentity : Bool
    periodicTableRecoveryDeterminesMolecularIdentityIsFalse :
      periodicTableRecoveryDeterminesMolecularIdentity ≡ false

    valenceClassDeterminesReactionPath : Bool
    valenceClassDeterminesReactionPathIsFalse :
      valenceClassDeterminesReactionPath ≡ false

    molecularFormulaDeterminesGeometryStereoAndEnvironment : Bool
    molecularFormulaDeterminesGeometryStereoAndEnvironmentIsFalse :
      molecularFormulaDeterminesGeometryStereoAndEnvironment ≡ false

    stoichiometricBalanceDeterminesKinetics : Bool
    stoichiometricBalanceDeterminesKineticsIsFalse :
      stoichiometricBalanceDeterminesKinetics ≡ false

    admissibleReactionDeterminesPlantYield : Bool
    admissibleReactionDeterminesPlantYieldIsFalse :
      admissibleReactionDeterminesPlantYield ≡ false

    sameNominalProductDeterminesUpstreamProcessHistory : Bool
    sameNominalProductDeterminesUpstreamProcessHistoryIsFalse :
      sameNominalProductDeterminesUpstreamProcessHistory ≡ false

    sameStartingCompositionDeterminesTemporalChemicalFibre : Bool
    sameStartingCompositionDeterminesTemporalChemicalFibreIsFalse :
      sameStartingCompositionDeterminesTemporalChemicalFibre ≡ false

    quantitativeChemistryNeedsDownstreamReceipts : Bool
    quantitativeChemistryNeedsDownstreamReceiptsIsTrue :
      quantitativeChemistryNeedsDownstreamReceipts ≡ true

canonicalAtomicChemistryCrossPollinationBoundary :
  AtomicChemistryCrossPollinationBoundary
canonicalAtomicChemistryCrossPollinationBoundary =
  atomicChemistryCrossPollinationBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl

------------------------------------------------------------------------
-- Highest-alpha weld contract for the present atomic programme.
------------------------------------------------------------------------

record AtomicToIndustrialChemistryFrontier : Set where
  constructor atomicToIndustrialChemistryFrontier
  field
    structuralAtomicLayer : String
    firstPhysicalAtomicLayer : String
    molecularBridge : String
    reactionBridge : String
    processBridge : String
    temporalFibreRule : String
    firstConcretePetrochemicalTarget : String
    firstConcreteMolecularTarget : String
    nextPromotionGate : String

canonicalAtomicToIndustrialChemistryFrontier : AtomicToIndustrialChemistryFrontier
canonicalAtomicToIndustrialChemistryFrontier =
  atomicToIndustrialChemistryFrontier
    "AtomicPeriodicTable369 exact Madelung/period/closure owners plus H/He physical validation ladder"
    "same-object radial identity, hydrogen reference diagnostics and helium Hartree/HF-limit convergence"
    "consume MolecularAssemblyBoundary: bond, geometry, charge, stereochemistry and environment are new obligations"
    "consume TransitionKernel + AdmissibleReactionTransitionBridgeExact: conservation and enablement before kinetics"
    "consume SaltPetroleumIndustrialChemistryNetworkExact: process kind, feedstock, separation, safety, yield, quality and lot history"
    "state is a dependent fibre over time; identical nominal species/product labels do not identify histories"
    "ethylene/chlorine -> EDC -> VCM -> PVC, because it literally joins hydrocarbon and salt-derived atomic/material families while preserving process non-collapse"
    "carbon-bearing small molecules and Allium organosulfur species, because existing identity/trajectory owners expose valence, geometry and time-indexed chemistry gaps"
    "derive/measure molecule-specific electronic structure and reaction energetics, then attach kinetics/operating-envelope/empirical receipts; do not jump from periodicity directly to industrial chemistry"

-- Importing Physical is itself intentional: a checker of this bridge also sees
-- the current atomic physical-validation cone.  No claim is made merely from
-- import presence.
physicalValidationImported : Bool
physicalValidationImported = true
