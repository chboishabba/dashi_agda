module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseAtomisticConfigurationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Physics.Chemistry.AtomicPeriodicTable369GenerativeExact as Atomic369
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSIQuantityBridgeExact as SIAdK
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCalibrationAttributionEnvelopeExact as Attr
import DASHI.Physics.Units.SI as SI

------------------------------------------------------------------------
-- ADK ATOMISTIC CONFIGURATION CARRIER
--
-- Geometry starts at indexed atoms, not at an abstract protein graph.  This
-- owner deliberately stops before force-field/dynamics semantics: a structural
-- configuration can exist without paying a mechanics context.
------------------------------------------------------------------------

atomicElementIdentitySurface : Set
atomicElementIdentitySurface = Atomic369.AtomicIndex

articleDOI = Attr.articleDOI
adkQID = Attr.adkQID
adkUniProt = Attr.adkUniProt
openPDB = Attr.openPDB
closedPDB = Attr.closedPDB

------------------------------------------------------------------------
-- Atomic-mass source attribution.
--
-- Prohaska et al., Standard atomic weights of the elements 2021,
-- Pure and Applied Chemistry 94 (2022), DOI 10.1515/pac-2019-0603.
--
-- Standard/abridged atomic weight is a mass convention for normal terrestrial
-- material.  It is not an exact isotope mass and it is not implied by atom,
-- PubChem, PDB, QID or UniProt identity.
------------------------------------------------------------------------

atomicMassSource : Attribution.AttributedSource
atomicMassSource =
  Attribution.mkDOISource
    "Prohaska et al."
    "Standard atomic weights of the elements 2021"
    "Pure and Applied Chemistry"
    "2022"
    "10.1515/pac-2019-0603"
    "https://doi.org/10.1515/pac-2019-0603"
    Attribution.academicArticleSource
    "pays the cited standard/abridged atomic-weight convention only; DASHI uses a rounded integer carrier for geometry weighting and does not promote it to exact isotope mass"
    Attribution.publicAttribution

atomicMassArticleQID : Identity.ExternalIdentityDemand
atomicMassArticleQID =
  Identity.mkOptionalIdentityDemand
    "AdK atomistic configuration mass weighting"
    "Prohaska et al. 2021 standard atomic weights article QID"
    "Standard atomic weights of the elements 2021"
    Identity.wikidataQid
    (Identity.unresolved "article-level QID not independently verified in this tranche")

atomicMassDeweyCoordinate : String
atomicMassDeweyCoordinate =
  "exact source-item Dewey coordinate unresolved; DOI retained as primary bibliographic identity"

record AtomicMassConvention : Set where
  constructor atomic-mass-convention
  field
    source : Attribution.AttributedSource
    qid : Identity.ExternalIdentityDemand
    deweyCoordinate : String
    numericScale : String
    isotopeScope : String
    conventionRole : String
open AtomicMassConvention public

canonicalAtomicMassConvention : AtomicMassConvention
canonicalAtomicMassConvention = atomic-mass-convention
  atomicMassSource
  atomicMassArticleQID
  atomicMassDeweyCoordinate
  "abridged standard atomic weight rounded to 0.001 u and stored as milli-u"
  "normal terrestrial material convention; not isotope-resolved"
  "mass weighting input for a COM evaluator; not atomic identity and not force-field mass authority"

record ElementMassEntry : Set where
  constructor element-mass-entry
  field
    elementLabel : String
    protonNumber : Nat
    milliUnifiedAtomicMassUnits : Nat
    convention : AtomicMassConvention
    sourceReading : String
open ElementMassEntry public

hydrogenMass : ElementMassEntry
hydrogenMass = element-mass-entry "H" 1 1008 canonicalAtomicMassConvention "abridged standard atomic weight 1.008"

carbonMass : ElementMassEntry
carbonMass = element-mass-entry "C" 6 12011 canonicalAtomicMassConvention "abridged standard atomic weight 12.011"

nitrogenMass : ElementMassEntry
nitrogenMass = element-mass-entry "N" 7 14007 canonicalAtomicMassConvention "abridged standard atomic weight 14.007"

oxygenMass : ElementMassEntry
oxygenMass = element-mass-entry "O" 8 15999 canonicalAtomicMassConvention "abridged standard atomic weight 15.999"

magnesiumMass : ElementMassEntry
magnesiumMass = element-mass-entry "Mg" 12 24305 canonicalAtomicMassConvention "abridged standard atomic weight 24.305"

phosphorusMass : ElementMassEntry
phosphorusMass = element-mass-entry "P" 15 30974 canonicalAtomicMassConvention "30.973761998 rounded to 30.974 for the milli-u carrier"

sulfurMass : ElementMassEntry
sulfurMass = element-mass-entry "S" 16 32060 canonicalAtomicMassConvention "abridged standard atomic weight 32.06"

canonicalBiomolecularMassEntries : List ElementMassEntry
canonicalBiomolecularMassEntries =
  hydrogenMass ∷ carbonMass ∷ nitrogenMass ∷ oxygenMass ∷
  magnesiumMass ∷ phosphorusMass ∷ sulfurMass ∷ []

------------------------------------------------------------------------
-- Indexed atom/topology/coordinate carrier.
------------------------------------------------------------------------

record AtomSiteIdentity : Set where
  constructor atom-site-identity
  field
    stableAtomIndex : Nat
    elementProtonNumber : Nat
    elementSymbol : String
    residueNumber : Nat
    residueName : String
    chainId : String
    atomName : String
    componentName : String
    chemicalRole : String
open AtomSiteIdentity public

record CartesianCoordinate : Set where
  constructor cartesian-coordinate
  field
    x y z : SI.Quantity SI.Length SIAdK.angstromScale
open CartesianCoordinate public

record CoordinateEntry : Set where
  constructor coordinate-entry
  field
    atomIndex : Nat
    position : CartesianCoordinate
open CoordinateEntry public

record AtomisticTopology : Set where
  constructor atomistic-topology
  field
    atoms : List AtomSiteIdentity
    connectivityReference : String
    sequenceReference : String
    topologyProvenance : String
open AtomisticTopology public

record ChemicalMicrostate : Set where
  constructor chemical-microstate
  field
    ligandOccupancyReference : String
    protonationReference : String
    formalChargeReference : String
    magnesiumOccupancyReference : String
    magnesiumCoordinationReference : String
    microstateSourceReference : String
    microstatePaid : Bool
open ChemicalMicrostate public

record PeriodicBoxContext : Set where
  constructor periodic-box-context
  field
    boxRole : String
    boxGeometryReference : String
    periodicBoundaryApplied : Bool
open PeriodicBoxContext public

record AtomisticConfiguration : Set where
  constructor atomistic-configuration
  field
    topology : AtomisticTopology
    chemicalMicrostate : ChemicalMicrostate
    coordinates : List CoordinateEntry
    boxContext : PeriodicBoxContext
    structureObjectIdentity : String
    coordinateSourceReference : String
    provenanceReference : String
open AtomisticConfiguration public

------------------------------------------------------------------------
-- Validity is proof-relevant.  We do not decide these obligations by citation.
------------------------------------------------------------------------

record ValidAdKConfiguration (configuration : AtomisticConfiguration) : Set₁ where
  constructor valid-adk-configuration
  field
    stableAtomIndicesUnique : Set
    everyCoordinateIndexResolvesInTopology : Set
    selectedAtomsHaveCoordinates : Set
    elementMassLookupTotalOnSelectedAtoms : Set
    topologyAndCoordinatesSameObject : Set
    chemicalMicrostateScopeRetained : Set
open ValidAdKConfiguration public

------------------------------------------------------------------------
-- WrongType / attribution firewalls.
------------------------------------------------------------------------

data ConfigurationDeterminesMechanicsContext : Set where
data RegistryIdentityDeterminesAtomicMassConvention : Set where
data StandardAtomicWeightIsExactIsotopeMass : Set where
data PDBIdentityCreatesCoordinates : Set where
\data DOIIdentityCreatesAtomicMassValue : Set where

configurationDoesNotDetermineMechanics : ConfigurationDeterminesMechanicsContext → ⊥
configurationDoesNotDetermineMechanics ()

registryIdentityDoesNotDetermineMassConvention : RegistryIdentityDeterminesAtomicMassConvention → ⊥
registryIdentityDoesNotDetermineMassConvention ()

standardAtomicWeightDoesNotBecomeExactIsotopeMass : StandardAtomicWeightIsExactIsotopeMass → ⊥
standardAtomicWeightDoesNotBecomeExactIsotopeMass ()

pdbIdentityDoesNotCreateCoordinates : PDBIdentityCreatesCoordinates → ⊥
pdbIdentityDoesNotCreateCoordinates ()

doiIdentityDoesNotCreateAtomicMassValue : DOIIdentityCreatesAtomicMassValue → ⊥
doiIdentityDoesNotCreateAtomicMassValue ()

record AdKAtomisticConfigurationBoundary : Set where
  constructor adk-atomistic-configuration-boundary
  field
    stableAtomIndexRetained : Bool
    atomicIdentityRetained : Bool
    topologySeparatedFromCoordinates : Bool
    chemicalMicrostateRetained : Bool
    threeDimensionalCoordinatesTypedAsSILength : Bool
    boxContextRetained : Bool
    provenanceRetained : Bool
    atomicMassConventionExplicitlyAttributed : Bool
    atomicMassQidExplicitlyUnresolved : Bool
    atomicMassDeweyExplicitlyUnresolved : Bool
    configurationDeterminesMechanicsContext : Bool
    registryIdentityDeterminesAtomicMassConvention : Bool
    standardAtomicWeightEqualsExactIsotopeMass : Bool
    pdbIdentityCreatesCoordinates : Bool
    doiIdentityCreatesAtomicMassValue : Bool
open AdKAtomisticConfigurationBoundary public

canonicalAdKAtomisticConfigurationBoundary : AdKAtomisticConfigurationBoundary
canonicalAdKAtomisticConfigurationBoundary =
  adk-atomistic-configuration-boundary
    true true true true true true true true true true
    false false false false false
