module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinasePDBAtomisticFixtureExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseAtomisticConfigurationExact as Config
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseConformationalEmpiricalExact as Empirical
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseStructuralIdentitySnowballExact as Structural
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSourcePaidThreeCVEndpointExact as Endpoint
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCalibrationAttributionEnvelopeExact as Attr

------------------------------------------------------------------------
-- PDB SAME-OBJECT FIXTURE ENVELOPE
--
-- A PDB entry identifier does not identify one unique evaluated configuration.
-- Both 4AKE and 1AKE contain chains/copies A and B.  Therefore entry identity,
-- coordinate manifestation, model/chain choice, altloc policy, chemical
-- microstate and any derived CV observation remain separate receipts.
------------------------------------------------------------------------

articleDOI = Attr.articleDOI
articleQID = Attr.articleQID
adkQID = Structural.adkQid
adkUniProt = Structural.adkUniProt

record PDBCoordinateManifestation : Set where
  constructor pdb-coordinate-manifestation
  field
    pdbLabel : String
    pdbDepositionDOI : String
    source : Attribution.AttributedSource
    coordinateFormat : String
    canonicalCoordinateURL : String
    modelSelection : String
    chainSelection : String
    alternateLocationPolicy : String
    hydrogenPolicy : String
    ligandWaterPolicy : String
    coordinateRevisionReference : String
    coordinateBytesAcquiredIntoFormalFixture : Bool
    selectedChainPaidByAdKCVSource : Bool
    interpretation : String
open PDBCoordinateManifestation public

open4AKEManifestation : PDBCoordinateManifestation
open4AKEManifestation = pdb-coordinate-manifestation
  "4AKE"
  "10.2210/pdb4AKE/pdb"
  Structural.open4AKESource
  "wwPDB/RCSB coordinate entry; exact local byte manifestation not embedded in this Agda owner"
  "https://files.rcsb.org/download/4AKE.cif"
  "X-ray entry; model selection must be explicit before atom indices are generated"
  "entry contains protein chains A and B; Li-Liu-Ji endpoint role does not by itself choose one chain in this fixture"
  "must be explicit when coordinates contain alternate locations"
  "PDB experiment does not make simulation hydrogen/protonation placement definitional"
  "water/heterogen inclusion must be explicit for any atomistic configuration"
  "RCSB entry/revision identity retained; evaluator receipt must pin the actual bytes/revision it consumes"
  false false
  "4AKE is the source-paid open structural reference; PDB identity alone does not create the coordinate list or select chain A/B"

closed1AKEManifestation : PDBCoordinateManifestation
closed1AKEManifestation = pdb-coordinate-manifestation
  "1AKE"
  "10.2210/pdb1AKE/pdb"
  Structural.closed1AKESource
  "wwPDB/RCSB coordinate entry; exact local byte manifestation not embedded in this Agda owner"
  "https://files.rcsb.org/download/1AKE.cif"
  "X-ray entry; model selection must be explicit before atom indices are generated"
  "entry contains two copies/chains A and B; Muller-Schulz report two complexes in the asymmetric unit, one less well ordered"
  "must be explicit when coordinates contain alternate locations"
  "experimental heavy-atom coordinates do not define a simulation protonation assignment"
  "Ap5A/water inclusion and any later Mg/nucleotide simulation chemistry must remain explicit"
  "RCSB entry/revision identity retained; evaluator receipt must pin the actual bytes/revision it consumes"
  false false
  "1AKE is the source-paid closed/Ap5A structural reference; the two-copy crystal does not manufacture one canonical chain"

------------------------------------------------------------------------
-- Source-reported endpoint observations remain distinct from a recomputation.
------------------------------------------------------------------------

openEndpointObservation : Endpoint.ThreeCVEndpoint
openEndpointObservation = Endpoint.openEndpoint

closedEndpointObservation : Endpoint.ThreeCVEndpoint
closedEndpointObservation = Endpoint.closedEndpoint

record PDBAtomisticFixture : Set where
  constructor pdb-atomistic-fixture
  field
    manifestation : PDBCoordinateManifestation
    endpointObservation : Endpoint.ThreeCVEndpoint
    configurationCarrier : Set
    configurationRole : String
    entryIdentityAndEndpointSameStructuralRole : Bool
    coordinateBytesPinned : Bool
    chainSelectionPaid : Bool
    exactDLnAtomSubsetPaid : Bool
    threeCVRecomputedFromCoordinates : Bool
    recomputationAgreementWithSourceEndpointPaid : Bool
open PDBAtomisticFixture public

open4AKEFixture : PDBAtomisticFixture
open4AKEFixture = pdb-atomistic-fixture
  open4AKEManifestation
  openEndpointObservation
  Config.AtomisticConfiguration
  "future concrete configuration must be constructed from one pinned 4AKE coordinate manifestation plus explicit model/chain/altloc/chemical-context choices"
  true false false false false false

closed1AKEFixture : PDBAtomisticFixture
closed1AKEFixture = pdb-atomistic-fixture
  closed1AKEManifestation
  closedEndpointObservation
  Config.AtomisticConfiguration
  "future concrete configuration must be constructed from one pinned 1AKE coordinate manifestation plus explicit model/chain/altloc/chemical-context choices"
  true false false false false false

------------------------------------------------------------------------
-- External-identity coordinates remain navigational/provenance data.
------------------------------------------------------------------------

openPDBObjectQID : Identity.ExternalIdentityDemand
openPDBObjectQID = Structural.openPdbObjectQid

closedPDBObjectQID : Identity.ExternalIdentityDemand
closedPDBObjectQID = Structural.closedPdbObjectQid

pdbFixtureDeweyCoordinate : String
pdbFixtureDeweyCoordinate =
  "exact structure-entry/source-manifestation Dewey coordinate unresolved; PDB IDs and deposition DOIs retained separately"

------------------------------------------------------------------------
-- WrongType / attribution firewalls.
------------------------------------------------------------------------

data PDBEntryIdentitySelectsCanonicalChain : Set where
data SourceEndpointTripleEqualsCoordinateRecomputation : Set where
data PDBCoordinatesCreateSimulationHydrogens : Set where
data StructuralRoleCreatesChemicalMicrostate : Set where
data ApproximateEndpointCreatesExactCoordinateEquality : Set where

pdbEntryDoesNotSelectCanonicalChain : PDBEntryIdentitySelectsCanonicalChain → ⊥
pdbEntryDoesNotSelectCanonicalChain ()

sourceEndpointDoesNotEqualRecomputationByIdentity : SourceEndpointTripleEqualsCoordinateRecomputation → ⊥
sourceEndpointDoesNotEqualRecomputationByIdentity ()

pdbCoordinatesDoNotCreateSimulationHydrogens : PDBCoordinatesCreateSimulationHydrogens → ⊥
pdbCoordinatesDoNotCreateSimulationHydrogens ()

structuralRoleDoesNotCreateChemicalMicrostate : StructuralRoleCreatesChemicalMicrostate → ⊥
structuralRoleDoesNotCreateChemicalMicrostate ()

approximateEndpointDoesNotCreateExactCoordinateEquality : ApproximateEndpointCreatesExactCoordinateEquality → ⊥
approximateEndpointDoesNotCreateExactCoordinateEquality ()

record AdKPDBAtomisticFixtureBoundary : Set where
  constructor adk-pdb-atomistic-fixture-boundary
  field
    openAndClosedPdbObjectsRetained : Bool
    coordinateManifestationSeparatedFromEntryIdentity : Bool
    multiChainAmbiguityRetained : Bool
    modelAltlocHydrogenPoliciesExplicit : Bool
    sourceEndpointTriplesRetained : Bool
    pdbObjectQidsRetainedAsUnresolvedWhereApplicable : Bool
    deweyCoordinateExplicitlyUnresolved : Bool
    coordinateBytesAcquiredIntoAgdaFixture : Bool
    pdbEntryIdentitySelectsCanonicalChain : Bool
    sourceEndpointTripleEqualsCoordinateRecomputation : Bool
    pdbCoordinatesCreateSimulationHydrogens : Bool
    structuralRoleCreatesChemicalMicrostate : Bool
open AdKPDBAtomisticFixtureBoundary public

canonicalAdKPDBAtomisticFixtureBoundary : AdKPDBAtomisticFixtureBoundary
canonicalAdKPDBAtomisticFixtureBoundary =
  adk-pdb-atomistic-fixture-boundary
    true true true true true true true
    false false false false false
