module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinasePhysicalAttributionCoordinatesExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.DashiKnowledgeTraversalFunnelExact as Knowledge
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCalibrationAttributionEnvelopeExact as Attr
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseStructuralIdentitySnowballExact as Structural

------------------------------------------------------------------------
-- TYPED DOI / QID / DEWEY COORDINATES FOR THE ADK PHYSICAL CONTINUATION
--
-- This is a navigation/provenance owner, not a scientific-payment owner.
-- It reuses DashiKnowledgeCoordinate so that DOI/QID/Dewey are no longer only
-- prose fields in the new atomistic/mechanics layer.  Unknown Dewey/QID values
-- remain literally unresolved rather than inferred from neighbouring classes.
------------------------------------------------------------------------

adkPhysicalBridgeCoordinate : Knowledge.DashiKnowledgeCoordinate
adkPhysicalBridgeCoordinate =
  Knowledge.dashi-knowledge-coordinate
    "DASHI/Physics/Chemistry/AtomicPeriodicTable369AdenylateKinasePhysicalDynamicsBridgeExact.agda"
    "AdK geometry-all-the-way-down physical bridge"
    "unresolved exact Dewey coordinate; biophysics/protein-dynamics neighbourhood does not pay a same-object classification"
    "Q356240"
    "Li-Liu-Ji 2015 DOI 10.1016/j.bpj.2015.06.059; PMID 26244746; PMCID PMC4572606"

liLiuJiArticleCoordinate : Knowledge.DashiKnowledgeCoordinate
liLiuJiArticleCoordinate =
  Knowledge.dashi-knowledge-coordinate
    "external primary source"
    "Li, Liu and Ji 2015 AdK conformational-dynamics article"
    "unresolved exact article-level Dewey coordinate"
    "unresolved exact article-level QID"
    "DOI 10.1016/j.bpj.2015.06.059; PMID 26244746; PMCID PMC4572606"

adkProteinCoordinate : Knowledge.DashiKnowledgeCoordinate
adkProteinCoordinate =
  Knowledge.dashi-knowledge-coordinate
    "DASHI/Physics/Chemistry/AtomicPeriodicTable369AdenylateKinaseStructuralIdentitySnowballExact.agda"
    "E. coli adenylate kinase protein/enzyme identity"
    "unresolved exact protein-item Dewey coordinate"
    "Q356240"
    "UniProt P69441; external identifiers are identity coordinates only"

open4AKECoordinate : Knowledge.DashiKnowledgeCoordinate
open4AKECoordinate =
  Knowledge.dashi-knowledge-coordinate
    "external structural manifestation"
    "PDB 4AKE open/unligated E. coli adenylate kinase"
    "unresolved exact structure-entry Dewey coordinate"
    "unresolved exact PDB-object QID"
    "PDB 4AKE; deposition DOI 10.2210/pdb4AKE/pdb"

closed1AKECoordinate : Knowledge.DashiKnowledgeCoordinate
closed1AKECoordinate =
  Knowledge.dashi-knowledge-coordinate
    "external structural manifestation"
    "PDB 1AKE closed/Ap5A-bound E. coli adenylate kinase"
    "unresolved exact structure-entry Dewey coordinate"
    "unresolved exact PDB-object QID"
    "PDB 1AKE; deposition DOI 10.2210/pdb1AKE/pdb"

atomicMassCoordinate : Knowledge.DashiKnowledgeCoordinate
atomicMassCoordinate =
  Knowledge.dashi-knowledge-coordinate
    "DASHI/Physics/Chemistry/AtomicPeriodicTable369AdenylateKinaseAtomisticConfigurationExact.agda"
    "Prohaska et al. standard/abridged atomic-weight convention used for COM weighting"
    "unresolved exact source-item Dewey coordinate"
    "unresolved exact article-level QID"
    "DOI 10.1515/pac-2019-0603"

ffamber03Coordinate : Knowledge.DashiKnowledgeCoordinate
ffamber03Coordinate =
  Knowledge.dashi-knowledge-coordinate
    "DASHI/Physics/Chemistry/AtomicPeriodicTable369AdenylateKinaseHistoricalMechanicsExact.agda"
    "AMBER ff03/ffamber03 method lineage"
    "unresolved exact article/method Dewey coordinate"
    "unresolved exact article-level QID"
    "Duan et al. DOI 10.1002/jcc.10349"

polyphosphateParameterCoordinate : Knowledge.DashiKnowledgeCoordinate
polyphosphateParameterCoordinate =
  Knowledge.dashi-knowledge-coordinate
    "DASHI/Physics/Chemistry/AtomicPeriodicTable369AdenylateKinaseHistoricalMechanicsExact.agda"
    "Meagher-Redman-Carlson polyphosphate parameter method lineage"
    "unresolved exact article/method Dewey coordinate"
    "unresolved exact article-level QID"
    "DOI 10.1002/jcc.10262"

tip3pCoordinate : Knowledge.DashiKnowledgeCoordinate
tip3pCoordinate =
  Knowledge.dashi-knowledge-coordinate
    "DASHI/Physics/Chemistry/AtomicPeriodicTable369AdenylateKinaseHistoricalMechanicsExact.agda"
    "TIP3P water-model method lineage"
    "unresolved exact article/method Dewey coordinate"
    "unresolved exact article-level QID"
    "Jorgensen et al. DOI 10.1063/1.445869"

pmeCoordinate : Knowledge.DashiKnowledgeCoordinate
pmeCoordinate =
  Knowledge.dashi-knowledge-coordinate
    "DASHI/Physics/Chemistry/AtomicPeriodicTable369AdenylateKinaseHistoricalMechanicsExact.agda"
    "smooth particle-mesh Ewald method lineage"
    "unresolved exact article/method Dewey coordinate"
    "unresolved exact article-level QID"
    "Essmann et al. DOI 10.1063/1.470117"

noseHooverCoordinate : Knowledge.DashiKnowledgeCoordinate
noseHooverCoordinate =
  Knowledge.dashi-knowledge-coordinate
    "DASHI/Physics/Chemistry/AtomicPeriodicTable369AdenylateKinaseHistoricalMechanicsExact.agda"
    "Nose-Hoover thermostat method lineage"
    "unresolved exact article/method Dewey coordinate"
    "unresolved exact article-level QID"
    "Hoover DOI 10.1103/PhysRevA.31.1695; Nose lineage retained by method name pending a separately acquired source coordinate"

parrinelloRahmanCoordinate : Knowledge.DashiKnowledgeCoordinate
parrinelloRahmanCoordinate =
  Knowledge.dashi-knowledge-coordinate
    "DASHI/Physics/Chemistry/AtomicPeriodicTable369AdenylateKinaseHistoricalMechanicsExact.agda"
    "Parrinello-Rahman pressure/cell-dynamics method lineage"
    "unresolved exact article/method Dewey coordinate"
    "unresolved exact article-level QID"
    "DOI 10.1063/1.328693"

lincsCoordinate : Knowledge.DashiKnowledgeCoordinate
lincsCoordinate =
  Knowledge.dashi-knowledge-coordinate
    "DASHI/Physics/Chemistry/AtomicPeriodicTable369AdenylateKinaseHistoricalMechanicsExact.agda"
    "LINCS constraint-method lineage"
    "unresolved exact article/method Dewey coordinate"
    "unresolved exact article-level QID"
    "DOI 10.1002/(SICI)1096-987X(199709)18:12<1463::AID-JCC4>3.0.CO;2-H"

gromacs4Coordinate : Knowledge.DashiKnowledgeCoordinate
gromacs4Coordinate =
  Knowledge.dashi-knowledge-coordinate
    "DASHI/Physics/Chemistry/AtomicPeriodicTable369AdenylateKinaseHistoricalMechanicsExact.agda"
    "GROMACS 4 software-method lineage"
    "unresolved exact article/software Dewey coordinate"
    "unresolved exact article/software QID"
    "Hess et al. DOI 10.1021/ct700301q"

openMMCoordinate : Knowledge.DashiKnowledgeCoordinate
openMMCoordinate =
  Knowledge.dashi-knowledge-coordinate
    "DASHI/Physics/Chemistry/AtomicPeriodicTable369AdenylateKinaseOpenMMCVOracleExact.agda"
    "OpenMM executable CV-oracle capability"
    "unresolved exact software/documentation Dewey coordinate"
    "unresolved exact software QID"
    "OpenMM 8.6 CustomCentroidBondForce/CustomCVForce documentation; capability coordinate only"

physicalAttributionCoordinates : List Knowledge.DashiKnowledgeCoordinate
physicalAttributionCoordinates =
  adkPhysicalBridgeCoordinate ∷ liLiuJiArticleCoordinate ∷ adkProteinCoordinate ∷
  open4AKECoordinate ∷ closed1AKECoordinate ∷ atomicMassCoordinate ∷
  ffamber03Coordinate ∷ polyphosphateParameterCoordinate ∷ tip3pCoordinate ∷
  pmeCoordinate ∷ noseHooverCoordinate ∷ parrinelloRahmanCoordinate ∷
  lincsCoordinate ∷ gromacs4Coordinate ∷ openMMCoordinate ∷ []

------------------------------------------------------------------------
-- Attribution firewalls.
------------------------------------------------------------------------

data ExternalIdentityCreatesScientificPayment : Set where
data DeweyAdjacencyCreatesScientificDependency : Set where
data QidCreatesSameObjectWeld : Set where

externalIdentityDoesNotCreateScientificPayment : ExternalIdentityCreatesScientificPayment → ⊥
externalIdentityDoesNotCreateScientificPayment ()

deweyAdjacencyDoesNotCreateScientificDependency : DeweyAdjacencyCreatesScientificDependency → ⊥
deweyAdjacencyDoesNotCreateScientificDependency ()

qidDoesNotCreateSameObjectWeld : QidCreatesSameObjectWeld → ⊥
qidDoesNotCreateSameObjectWeld ()

record AdKPhysicalAttributionCoordinatesBoundary : Set where
  constructor adk-physical-attribution-coordinates-boundary
  field
    usesTypedDashiKnowledgeCoordinates : Bool
    doiQidDeweyRemainCoordinatesOnly : Bool
    unresolvedDeweyRemainsExplicit : Bool
    unresolvedQidRemainsExplicit : Bool
    existingAdkQidRetained : Bool
    existingPdbAndUniprotIdentityRetained : Bool
    externalIdentityCreatesScientificPayment : Bool
    deweyAdjacencyCreatesScientificDependency : Bool
    qidCreatesSameObjectWeld : Bool
open AdKPhysicalAttributionCoordinatesBoundary public

canonicalAdKPhysicalAttributionCoordinatesBoundary : AdKPhysicalAttributionCoordinatesBoundary
canonicalAdKPhysicalAttributionCoordinatesBoundary =
  adk-physical-attribution-coordinates-boundary
    true true true true true true
    false false false

-- Thin witnesses that the existing typed identity owners remain authoritative.
articleIdentitySurface = Attr.articleDOI
proteinIdentitySurface = Structural.adkUniProt
