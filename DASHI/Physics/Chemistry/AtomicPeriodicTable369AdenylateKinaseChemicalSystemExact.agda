module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseChemicalSystemExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Chemistry.TransitionKernel as Chemistry
import DASHI.Physics.Chemistry.AtomicPeriodicTable369ChemistryHyperfibreBridgeExact as Hyper
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCalibrationAttributionEnvelopeExact as Attr
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseConformationalEmpiricalExact as Structure

------------------------------------------------------------------------
-- ADENYLATE-KINASE CHEMICAL-SYSTEM IDENTITY / CONTEXT BRIDGE
--
-- The chemistry ontology is not duplicated here.  Species/reaction/environment
-- roles are the canonical DASHI.Chemistry.TransitionKernel carriers, while the
-- atomic->species->molecule proof obligations are reused from the existing 369
-- chemistry hyperfibre.
--
-- PubChem CIDs below are registry coordinates for the parent/reference entries
-- inspected 2026-09-17.  They do NOT choose the protonation/charge state used
-- in a simulation, Mg2+ coordination, ligand occupancy, catalytic mechanism,
-- or a numeric parameter.  Article DOI/QID/PDB/UniProt obey the same firewall.
------------------------------------------------------------------------

chemicalSpeciesSurface : Set
chemicalSpeciesSurface = Chemistry.Species

chemicalTransitionSurface : Set
chemicalTransitionSurface = Chemistry.Transition

chemicalEnvironmentSurface : Set
chemicalEnvironmentSurface = Chemistry.Environment

atomToSpeciesReceiptSurface : Set
atomToSpeciesReceiptSurface = Hyper.AtomicToSpeciesReceipt

speciesToMoleculeReceiptSurface : Set
speciesToMoleculeReceiptSurface = Hyper.SpeciesToMoleculeReceipt

articleDOI = Attr.articleDOI
adkQID = Attr.adkQID
adkUniProt = Attr.adkUniProt
openPDB = Attr.openPDB
closedPDB = Attr.closedPDB

record ChemicalRegistryIdentity : Set where
  constructor chemical-registry-identity
  field
    canonicalLabel : String
    registry : String
    registryIdentifier : String
    molecularFormula : String
    registrySourceLocator : String
    wikidataQidStatus : String
    protonationChargeReading : String
    role : String
open ChemicalRegistryIdentity public

atpIdentity : ChemicalRegistryIdentity
atpIdentity = chemical-registry-identity
  "adenosine 5'-triphosphate / 5'-ATP parent reference"
  "PubChem CID"
  "5957"
  "C10H16N5O13P3"
  "PubChem compound 5957, inspected 2026-09-17"
  "molecule-level QID not independently verified in this bridge"
  "registry parent entry; does not select the solution/simulation protonation state"
  "identity/navigation coordinate only"

ampIdentity : ChemicalRegistryIdentity
ampIdentity = chemical-registry-identity
  "adenosine 5'-monophosphate / AMP parent reference"
  "PubChem CID"
  "6083"
  "C10H14N5O7P"
  "PubChem compound 6083, inspected 2026-09-17"
  "molecule-level QID not independently verified in this bridge"
  "registry parent entry; does not select the solution/simulation protonation state"
  "identity/navigation coordinate only"

adpIdentity : ChemicalRegistryIdentity
adpIdentity = chemical-registry-identity
  "adenosine 5'-diphosphate / ADP parent reference"
  "PubChem CID"
  "6022"
  "C10H15N5O10P2"
  "PubChem compound 6022, inspected 2026-09-17"
  "molecule-level QID not independently verified in this bridge"
  "registry parent entry; PubChem also has charge-state-specific records, so parent CID does not select simulation protonation"
  "identity/navigation coordinate only"

ap5aIdentity : ChemicalRegistryIdentity
ap5aIdentity = chemical-registry-identity
  "diadenosine pentaphosphate / Ap5A parent reference"
  "PubChem CID"
  "53477724"
  "C20H29N10O22P5"
  "PubChem compound 53477724, inspected 2026-09-17"
  "molecule-level QID not independently verified in this bridge"
  "registry parent entry; exact bound-state protonation is a separate obligation"
  "registry identity joined to the already source-paid 1AKE Ap5A-bound structural context"

magnesiumIdentity : ChemicalRegistryIdentity
magnesiumIdentity = chemical-registry-identity
  "magnesium(2+)"
  "PubChem CID"
  "888"
  "Mg+2"
  "PubChem compound 888, inspected 2026-09-17"
  "molecule/entity QID not independently verified in this bridge"
  "registry entry is explicitly Mg2+ but does not identify whether/where Mg2+ is coordinated in a particular AdK simulation or structure"
  "identity/navigation coordinate only; AdK-specific coordination requires a separate source receipt"

------------------------------------------------------------------------
-- Geometry-all-the-way-down receipt surfaces.
------------------------------------------------------------------------

adenylateAtomicToSpeciesReceipt : Hyper.AtomicToSpeciesReceipt
adenylateAtomicToSpeciesReceipt = Hyper.atomicToSpeciesReceipt
  "C/H/N/O/P element identities retained by the molecular formula registry coordinates"
  "species-specific charge/protonation remains an explicit context coordinate"
  "isotopic composition not selected by the parent registry identity"
  "valence/electronic constraints delegated to the canonical atomic/valence owners"
  "electronic state not reconstructed from PubChem CID"
  "ATP/AMP/ADP parent registry identities retained separately"
  "molecular formula retained; formula does not determine geometry"
  "same-object species weld requires source/context identity in addition to registry equality"

adenylateSpeciesToMoleculeReceipt : Hyper.SpeciesToMoleculeReceipt
adenylateSpeciesToMoleculeReceipt = Hyper.speciesToMoleculeReceipt
  "atom inventory constrained by retained molecular formula"
  "bond order / covalent structure belongs to the molecular identity layer"
  "3-D geometry is a distinct downstream coordinate"
  "stereochemistry is not recovered from a bare species label"
  "charge/protonation is not recovered from the parent CID alone"
  "solvent/ionic/ligand environment remains explicit"
  "stability under the declared environment is a separate empirical/model obligation"
  "observable identity requires the selected molecular manifestation and measurement/model role"

------------------------------------------------------------------------
-- AdK-specific contexts.  Binding/conformation and catalytic chemistry remain
-- different TransitionKernel roles.
------------------------------------------------------------------------

data AdKChemicalContext : Set where
  ligandFreeApoContext : AdKChemicalContext
  ap5aBoundStructuralContext : AdKChemicalContext
  nucleotideCatalyticContext : AdKChemicalContext
  magnesiumCoordinatedCatalyticContext : AdKChemicalContext

bindingRole : Chemistry.TransitionKind
bindingRole = Chemistry.bindingTransition

catalyticReactionRole : Chemistry.TransitionKind
catalyticReactionRole = Chemistry.chemicalReaction

catalyticStoichiometryTarget : String
catalyticStoichiometryTarget = "ATP + AMP <-> 2 ADP"

catalyticStoichiometryPayment : String
catalyticStoichiometryPayment =
  "chemical-system target retained for the AdK mechanism layer; this bridge does not promote exact protonation, Mg coordination, chemical potentials, or catalytic kinetics without a dedicated same-object source receipt"

structuralContextReading : String
structuralContextReading =
  "reuse AtomicPeriodicTable369AdenylateKinaseConformationalEmpiricalExact: 4AKE is open/unligated and 1AKE is closed/Ap5A-bound for the same E. coli AdK polypeptide; structural context is not phosphoryl-transfer chemistry"

------------------------------------------------------------------------
-- WrongType / attribution firewalls.
------------------------------------------------------------------------

data RegistryIdentitySelectsSimulationProtonation : Set where
data RegistryIdentitySelectsMgCoordination : Set where
data BindingConformationEqualsCatalyticChemistry : Set where
data IdentifierPresenceCreatesChemicalPayment : Set where
data PubChemIdentityCreatesThreeDimensionalGeometry : Set where

registryIdentityDoesNotSelectSimulationProtonation : RegistryIdentitySelectsSimulationProtonation → ⊥
registryIdentityDoesNotSelectSimulationProtonation ()

registryIdentityDoesNotSelectMgCoordination : RegistryIdentitySelectsMgCoordination → ⊥
registryIdentityDoesNotSelectMgCoordination ()

bindingConformationDoesNotEqualCatalyticChemistry : BindingConformationEqualsCatalyticChemistry → ⊥
bindingConformationDoesNotEqualCatalyticChemistry ()

identifierDoesNotCreateChemicalPayment : IdentifierPresenceCreatesChemicalPayment → ⊥
identifierDoesNotCreateChemicalPayment ()

pubChemIdentityDoesNotCreate3DGeometry : PubChemIdentityCreatesThreeDimensionalGeometry → ⊥
pubChemIdentityDoesNotCreate3DGeometry ()

record AdKChemicalSystemBoundary : Set where
  constructor adk-chemical-system-boundary
  field
    reusesCanonicalChemistryKernel : Bool
    reusesAtomicToMolecularHyperformalism : Bool
    atpAmpAdpRegistryIdentitiesRetained : Bool
    ap5aStructuralContextRetained : Bool
    magnesiumRegistryIdentityRetained : Bool
    atomToSpeciesReceiptExplicit : Bool
    speciesToMoleculeReceiptExplicit : Bool
    registryIdentitySelectsSimulationProtonation : Bool
    registryIdentitySelectsMgCoordination : Bool
    bindingConformationEqualsCatalyticChemistry : Bool
    identifierPresenceCreatesChemicalPayment : Bool
    pubChemIdentityCreatesThreeDimensionalGeometry : Bool
    exactCatalyticProtonationAndMgStatePaidHere : Bool
open AdKChemicalSystemBoundary public

canonicalAdKChemicalSystemBoundary : AdKChemicalSystemBoundary
canonicalAdKChemicalSystemBoundary =
  adk-chemical-system-boundary
    true true true true true true true
    false false false false false false
