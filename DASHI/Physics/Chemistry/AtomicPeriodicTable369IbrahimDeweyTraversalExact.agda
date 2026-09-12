module DASHI.Physics.Chemistry.AtomicPeriodicTable369IbrahimDeweyTraversalExact where

open import DASHI.Core.Prelude

import DASHI.Wikimedia.DashiKnowledgeTraversalFunnelExact as Ibrahim
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AttributionLedgerExact as Attribution

------------------------------------------------------------------------
-- IBRAHIM / DEWEY TRAVERSAL FOR THE ATOMIC SNOWBALL
--
-- Search policy donor:
-- Mark Ibrahim, Christopher M. Danforth, Peter Sheridan Dodds,
-- "Connecting every bit of knowledge: The structure of Wikipedia's First
-- Link Network", Journal of Computational Science 19 (2017), 21--30,
-- DOI 10.1016/j.jocs.2016.12.001, arXiv:1605.00309.
--
-- We reuse the existing DASHI first-link policy: explicit formulation owner
-- first, then typed dependency/generalisation. DOI, QID, Dewey and links are
-- search/identity coordinates only.  Dewey adjacency does not manufacture a
-- theorem edge and a nearest archive hit does not manufacture an executable
-- provenance receipt.
------------------------------------------------------------------------

periodicTableCoordinate : Ibrahim.DashiKnowledgeCoordinate
periodicTableCoordinate =
  Ibrahim.dashi-knowledge-coordinate
    "DASHI/Physics/Chemistry/AtomicPeriodicTable369GenerativeExact.agda"
    "generic Nat-indexed atom -> valence-recurrence periodic-table quotient"
    "546.8"
    "Q10693"
    "PR #886; current composition"

periodicRecoveryBoundaryCoordinate : Ibrahim.DashiKnowledgeCoordinate
periodicRecoveryBoundaryCoordinate =
  Ibrahim.dashi-knowledge-coordinate
    "DASHI/Physics/Chemistry/AtomicPeriodicTableRecoveryBoundary.agda"
    "typed physical recovery boundary"
    "546.8"
    "Q10693"
    "commit 554e8f930dfee5293d75d3bb67be8098bde088d3; PR #101"

chemicalElementCoordinate : Ibrahim.DashiKnowledgeCoordinate
chemicalElementCoordinate =
  Ibrahim.dashi-knowledge-coordinate
    "external semantic coordinate"
    "chemical element concept"
    "546"
    "Q11344"
    "https://www.wikidata.org/wiki/Q11344"

atomCoordinate : Ibrahim.DashiKnowledgeCoordinate
atomCoordinate =
  Ibrahim.dashi-knowledge-coordinate
    "DASHI/Physics/Foundations/AtomicFermionShellExact.agda"
    "atomic species plus fermionic shell carrier"
    "539.7"
    "Q9121"
    "https://www.wikidata.org/wiki/Q9121"

atomicOrbitalCoordinate : Ibrahim.DashiKnowledgeCoordinate
atomicOrbitalCoordinate =
  Ibrahim.dashi-knowledge-coordinate
    "external semantic / physical representation coordinate"
    "atomic orbital"
    "541.28"
    "Q53860"
    "https://www.wikidata.org/wiki/Q53860; IUPAC Gold Book A00500"

quantumMechanicsCoordinate : Ibrahim.DashiKnowledgeCoordinate
quantumMechanicsCoordinate =
  Ibrahim.dashi-knowledge-coordinate
    "external semantic / theory coordinate"
    "quantum mechanics"
    "530.12"
    "Q944"
    "https://www.wikidata.org/wiki/Q944"

carbonCoordinate : Ibrahim.DashiKnowledgeCoordinate
carbonCoordinate =
  Ibrahim.dashi-knowledge-coordinate
    "DASHI/Chemistry/CarbonChemicalSuitabilityLifeBoundaryExact.agda"
    "carbon chemical-suitability boundary"
    "547"
    "Q623"
    "https://www.wikidata.org/wiki/Q623; IUPAC Gold Book C00821"

ionizationEnergyCoordinate : Ibrahim.DashiKnowledgeCoordinate
ionizationEnergyCoordinate =
  Ibrahim.dashi-knowledge-coordinate
    "unresolved DASHI physical scale consumer"
    "first-ionization-energy validation target"
    "unresolved in inspected semantic source"
    "Q483769"
    "https://www.wikidata.org/wiki/Q483769; IUPAC Gold Book I03199; IEV 113-06-39"

hartreeFockCoordinate : Ibrahim.DashiKnowledgeCoordinate
hartreeFockCoordinate =
  Ibrahim.dashi-knowledge-coordinate
    "external method coordinate"
    "Hartree-Fock / self-consistent-field method family"
    "unresolved in inspected semantic source"
    "Q7879841"
    "https://www.wikidata.org/wiki/Q7879841"

historicalDashiQCoordinate : Ibrahim.DashiKnowledgeCoordinate
historicalDashiQCoordinate =
  Ibrahim.dashi-knowledge-coordinate
    "chboishabba/dashiQ README.md"
    "first located public periodic-table/kernel-filling programme statement"
    "546.8 / 539.7 topic coordinates"
    "Q10693 / Q9121 semantic coordinates"
    "commit bbedb3bed85e31125eb68255379b57788a434939; 2026-01-03T00:16:42Z"

historicalArchiveCoordinate : Ibrahim.DashiKnowledgeCoordinate
historicalArchiveCoordinate =
  Ibrahim.dashi-knowledge-coordinate
    "DASHI Atom conversation archive"
    "MDL/exclusion filling and closure-run provenance surface"
    "546.8 / 539.7 topic coordinates"
    "Q10693 / Q9121 semantic coordinates"
    "canonical archive thread id 25ec0d2e654f33ea6f524f816b4c465e86ef21cf"

------------------------------------------------------------------------
-- Typed first-link edges.  These are chosen explanatory/search parents, not
-- claims that Wikipedia/Dewey adjacency itself supplies the dependency.

currentToRecoveryBoundary : Ibrahim.DashiFirstLinkEdge
currentToRecoveryBoundary =
  Ibrahim.dashi-first-link-edge
    periodicTableCoordinate
    periodicRecoveryBoundaryCoordinate
    Ibrahim.dependsOn
    Ibrahim.canonicalDashiFirstLinkPolicy
    "the current generic constructor consumes the existing typed periodic-recovery boundary rather than replacing it"
    true

recoveryBoundaryToAtom : Ibrahim.DashiFirstLinkEdge
recoveryBoundaryToAtom =
  Ibrahim.dashi-first-link-edge
    periodicRecoveryBoundaryCoordinate
    atomCoordinate
    Ibrahim.dependsOn
    Ibrahim.canonicalDashiFirstLinkPolicy
    "periodic recovery requires an atomic species / shell carrier before valence recurrence can be interpreted"
    true

periodicTableToChemicalElement : Ibrahim.DashiFirstLinkEdge
periodicTableToChemicalElement =
  Ibrahim.dashi-first-link-edge
    periodicTableCoordinate
    chemicalElementCoordinate
    Ibrahim.externallyIdentifiedBy
    Ibrahim.canonicalDashiFirstLinkPolicy
    "Wikidata records chemical elements as the items classified by the periodic table; this is semantic navigation only"
    true

atomToAtomicOrbital : Ibrahim.DashiFirstLinkEdge
atomToAtomicOrbital =
  Ibrahim.dashi-first-link-edge
    atomCoordinate
    atomicOrbitalCoordinate
    Ibrahim.supportedBy
    Ibrahim.canonicalDashiFirstLinkPolicy
    "the shell-filling realization needs one-particle orbital representation data; QID/DDC only identify the external concept"
    true

atomicOrbitalToQuantumMechanics : Ibrahim.DashiFirstLinkEdge
atomicOrbitalToQuantumMechanics =
  Ibrahim.dashi-first-link-edge
    atomicOrbitalCoordinate
    quantumMechanicsCoordinate
    Ibrahim.supportedBy
    Ibrahim.canonicalDashiFirstLinkPolicy
    "orbital semantics are supplied by the quantum-mechanical representation layer, not by 369 cardinality alone"
    true

periodicProgrammeToDashiQSource : Ibrahim.DashiFirstLinkEdge
periodicProgrammeToDashiQSource =
  Ibrahim.dashi-first-link-edge
    periodicTableCoordinate
    historicalDashiQCoordinate
    Ibrahim.supportedBy
    Ibrahim.canonicalDashiFirstLinkPolicy
    "2026-01-03 dashiQ README is the earliest located public programme statement explicitly naming chemistry / periodic table as the first major test"
    true

archiveSupportsHistoricalRun : Ibrahim.DashiFirstLinkEdge
archiveSupportsHistoricalRun =
  Ibrahim.dashi-first-link-edge
    historicalDashiQCoordinate
    historicalArchiveCoordinate
    Ibrahim.crossPollinatesWith
    Ibrahim.canonicalDashiFirstLinkPolicy
    "archive supplies later retained details/code/run reports for the MDL filling lane; it is not silently treated as the same dated publication object"
    true

scaleFrontierToIonization : Ibrahim.DashiFirstLinkEdge
scaleFrontierToIonization =
  Ibrahim.dashi-first-link-edge
    periodicRecoveryBoundaryCoordinate
    ionizationEnergyCoordinate
    Ibrahim.generalisesTo
    Ibrahim.canonicalDashiFirstLinkPolicy
    "first quantitative consumer after structure is physical energy/ionization validation"
    true

ionizationToHartreeFock : Ibrahim.DashiFirstLinkEdge
ionizationToHartreeFock =
  Ibrahim.dashi-first-link-edge
    ionizationEnergyCoordinate
    hartreeFockCoordinate
    Ibrahim.supportedBy
    Ibrahim.canonicalDashiFirstLinkPolicy
    "historical self-consistent-field literature supplies a method family for the open operator-to-spectrum/scale bridge; DASHI same-object realization remains unpaid"
    true

------------------------------------------------------------------------
-- Snowball result from the archive inspection.
--
-- The archive contains actual code-shaped reconstructions and reported/rerun
-- Python experiments, including the n + alpha*l ordering, degeneracy
-- 2(2l+1), Z=2/10/18 closures, alpha-sensitivity at closure/residue, and toy
-- ionization-energy work.  But the first reconstruction explicitly says it is
-- reconstructing the earlier test.  Therefore it narrows the missing artifact
-- without paying original executable identity/hash.

record ArchiveExecutableSnowballStatus : Set where
  constructor archive-executable-snowball-status
  field
    embeddedCodeLocated : Bool
    embeddedRunNarrativeLocated : Bool
    simpleCostLocated : Bool
    closureCoordinatesLocated : Bool
    alphaSensitivityRunLocated : Bool
    toyIonizationRunLocated : Bool
    originalStandaloneScriptLocated : Bool
    originalArtifactHashLocated : Bool
    exactOriginalParameterScheduleLocated : Bool

canonicalArchiveExecutableSnowballStatus : ArchiveExecutableSnowballStatus
canonicalArchiveExecutableSnowballStatus =
  archive-executable-snowball-status
    true true true true true true false false false

record IbrahimDeweyTraversalBoundary : Set where
  constructor ibrahim-dewey-traversal-boundary
  field
    ibrahimDoi : String
    deweyAdjacencyPromotesDependency : Bool
    qidPromotesProof : Bool
    firstLinkPromotesTheorem : Bool
    archiveEmbeddedCodeEqualsOriginalArtifact : Bool
    methodLiteraturePaysDashiSameObjectBridge : Bool
    acquisitionMayFollowDeweyGraph : Bool

canonicalIbrahimDeweyTraversalBoundary : IbrahimDeweyTraversalBoundary
canonicalIbrahimDeweyTraversalBoundary =
  ibrahim-dewey-traversal-boundary
    "10.1016/j.jocs.2016.12.001"
    false false false false false true

------------------------------------------------------------------------
-- Current highest-alpha path after the Ibrahim/Dewey walk.

record IbrahimDeweyHighestAlphaFrontier : Set where
  constructor ibrahim-dewey-highest-alpha-frontier
  field
    historicalArtifactLeaf : String
    physicalLeaf : String
    acquiredPrimaryMethodSources : String
    unresolvedClassification : String
    paymentRule : String

canonicalIbrahimDeweyHighestAlphaFrontier : IbrahimDeweyHighestAlphaFrontier
canonicalIbrahimDeweyHighestAlphaFrontier =
  ibrahim-dewey-highest-alpha-frontier
    "extract/identify the original standalone MDL kernel-filling script or exact execution artifact behind the archive reports; embedded reconstructions narrow but do not pay this leaf"
    "construct the same-object operator-to-spectrum / calibrated ionization-energy bridge on the DASHI atomic carrier"
    "Hartree 1928 DOI 10.1017/S0305004100011920; Slater 1928 DOI 10.1103/PhysRev.32.339"
    "Dewey values for the ionization-energy and Hartree-Fock publication/method objects remain unresolved rather than inferred from neighbouring classes"
    "Ibrahim/Dewey/QID navigation chooses where to inspect next; only typed dependency and same-object/source receipts pay conclusions"

-- Thin import witness so the attribution owner remains the identifier authority.
attributionOwner : Set₁
attributionOwner = Attribution.AttributionReceipt
