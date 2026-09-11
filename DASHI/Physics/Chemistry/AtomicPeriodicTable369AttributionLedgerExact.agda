module DASHI.Physics.Chemistry.AtomicPeriodicTable369AttributionLedgerExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Chemistry.AtomicPeriodicTable369ChronologyVerificationExact as Chronology
import DASHI.Physics.Chemistry.AtomicPeriodicTable369ProvenanceSnowballExact as Provenance

------------------------------------------------------------------------
-- Snowball attribution ledger for the 369 atomic / periodic-table lane.
--
-- Every entry keeps bibliographic identity, semantic identity, source role,
-- Dewey classification cue, and direct locator separate.  Missing identifiers
-- remain explicit strings rather than being manufactured from adjacency.

record AttributionReceipt : Set where
  constructor attributionReceipt
  field
    author : String
    title : String
    year : String
    doi : String
    qid : String
    primaryStatus : String
    dewey : String
    directLink : String
    sourceObject : String
    authority : String
    relationship : String

open AttributionReceipt public

------------------------------------------------------------------------
-- Repo-native chronology receipts.

historicalDASHIAtomArchive : AttributionReceipt
historicalDASHIAtomArchive =
  attributionReceipt
    "Johl Brown / ChatGPT conversation archive"
    "DASHI Atom"
    "2026; exact first-source date unresolved"
    "unassigned"
    "unassigned"
    "primary internal programme source object; not external peer-reviewed literature"
    "539.7 / 546 classification cue"
    "attached conversation export; exact public permalink unresolved"
    "historical source object"
    "provenance authority for what the programme reported or attempted"
    "records atoms-as-dictionaries, MDL/exclusion filling, noble-gas-like closures, and the Z=2,10,18 historical regression"

firstAtomicSpectralTooling : AttributionReceipt
firstAtomicSpectralTooling =
  attributionReceipt
    "Johl Brown"
    "spectral line tooling and smoke tests"
    "2025-11-11"
    "unassigned"
    "atom Q9121; periodic table Q10693 used only as semantic coordinates"
    "primary repository implementation receipt"
    "539.7"
    "https://github.com/chboishabba/dashifine/commit/4f1441e4989beec157733a960ca7dfc47a2bf3ee"
    "chboishabba/dashifine commit 4f1441e4989beec157733a960ca7dfc47a2bf3ee"
    "implementation chronology authority"
    "earliest clean atomic/spectral implementation located in the current cross-repo audit; not yet the 369 periodic-table constructor"

projectionPhysicsProgramme : AttributionReceipt
projectionPhysicsProgramme =
  attributionReceipt
    "Johl Brown"
    "Physics Targets That Fit The Projection Framework"
    "2026-03-06"
    "unassigned"
    "unassigned"
    "primary repository programme document"
    "530 / 539 classification cue"
    "https://github.com/chboishabba/dashiQ/commit/47071bed2cbe853c76fb5bec7d65f3a8b73b14bc"
    "chboishabba/dashiQ PHYSICS_TARGETS.md at commit 47071bed2cbe853c76fb5bec7d65f3a8b73b14bc"
    "programme chronology authority"
    "explicit geometry/projection-to-effective-physics programme precursor; not itself atom recovery"

firstDirectAtomicClosureImplementation : AttributionReceipt
firstDirectAtomicClosureImplementation =
  attributionReceipt
    "Johl Brown"
    "atom/chemistry recovery carrier and shell-filling strengthening surface"
    "2026-04-30"
    "unassigned"
    "atom Q9121; periodic table Q10693"
    "primary repository formal implementation receipt"
    "539.7 / 546"
    "https://github.com/chboishabba/dashi_agda/commit/42e1d740141b0e9e1ca717ae5df79d6e31546c07"
    "chboishabba/dashi_agda commit 42e1d740141b0e9e1ca717ae5df79d6e31546c07"
    "implementation chronology authority"
    "earliest direct repo-native atom/chemistry closure milestone located in this audit; commit explicitly states staged closure rather than finished chemistry recovery"

explicitPeriodicRecoveryBoundary : AttributionReceipt
explicitPeriodicRecoveryBoundary =
  attributionReceipt
    "Johl Brown"
    "atomic periodic-table recovery boundary"
    "2026-07-19"
    "unassigned"
    "periodic table Q10693"
    "primary repository formal implementation receipt"
    "546"
    "https://github.com/chboishabba/dashi_agda/commit/554e8f930dfee5293d75d3bb67be8098bde088d3"
    "chboishabba/dashi_agda commit 554e8f930dfee5293d75d3bb67be8098bde088d3; PR #101"
    "formal recovery-boundary authority"
    "explicit shell-recurrence / periodic-table recovery owner; physical completion remains fail-closed"

leanBase369Mirror : AttributionReceipt
leanBase369Mirror =
  attributionReceipt
    "Johl Brown"
    "Lean mirror of Base369.agda"
    "current path introduced 2026-08-12; deeper pre-reorganization file lineage not yet paid"
    "unassigned"
    "unassigned"
    "primary repository cross-assistant implementation receipt"
    "511 / 530 classification cue"
    "https://github.com/chboishabba/dashi_lean4/blob/main/AgdaMirror/Base369.lean"
    "chboishabba/dashi_lean4 AgdaMirror/Base369.lean; current-path commit 72734285fd83387837e0025eb51a93b63629a0b9"
    "Lean proof-source authority for the finite 3/6/9 carrier laws only"
    "contains concrete proof terms for spin/modular XOR agreement, rotation orders, identities, and ternary associativity; does not yet mirror the atom constructor"

currentAtomicManuscript : AttributionReceipt
currentAtomicManuscript =
  attributionReceipt
    "Johl Brown / DASHI"
    "DASHI Atomic and Periodic-Table Formalism: Kernel Filling, MDL Selection, Valence Recurrence, and Provenance Gates"
    "2026-09-11"
    "unassigned; same-object DOI not yet located"
    "atom Q9121; periodic table Q10693; Pauli exclusion principle Q131594"
    "primary repository manuscript for the current consolidation"
    "539.7 / 546"
    "https://github.com/chboishabba/dashi_agda/pull/886"
    "Docs/papers/drafts/DASHIAtomicPeriodicTable369Formalism.tex on PR #886"
    "manuscript/provenance authority; not peer-review or empirical authority"
    "current paper-facing consolidation of the recovered constructor and its non-promotion boundaries"

------------------------------------------------------------------------
-- External primary / semantic anchors.

pauli1925 : AttributionReceipt
pauli1925 =
  attributionReceipt
    "Wolfgang Pauli"
    "Ueber den Zusammenhang des Abschlusses der Elektronengruppen im Atom mit der Komplexstruktur der Spektren"
    "1925"
    "10.1007/BF02980631"
    "Pauli exclusion principle Q131594"
    "primary historical physics paper"
    "539.7"
    "https://doi.org/10.1007/BF02980631"
    "Zeitschrift fuer Physik 31, 765-783"
    "primary scientific authority for the historical exclusion-principle source object"
    "external anchor for hard fermionic exclusion; citation does not identify DASHI's MDL cost with physical energy"

atomSemanticCoordinate : AttributionReceipt
atomSemanticCoordinate =
  attributionReceipt
    "Wikidata community"
    "atom"
    "current semantic item"
    "unassigned"
    "Q9121"
    "semantic authority only; not primary physics evidence"
    "539.7 classification cue"
    "https://www.wikidata.org/wiki/Q9121"
    "Wikidata item Q9121"
    "semantic identity coordinate"
    "machine-readable coordinate for the concept atom"

periodicTableSemanticCoordinate : AttributionReceipt
periodicTableSemanticCoordinate =
  attributionReceipt
    "Wikidata community"
    "periodic table"
    "current semantic item"
    "unassigned"
    "Q10693"
    "semantic authority only; not primary chemistry evidence"
    "546"
    "https://www.wikidata.org/wiki/Q10693"
    "Wikidata item Q10693"
    "semantic identity coordinate"
    "machine-readable coordinate for the periodic-table concept; Wikidata description itself encodes ordering by atomic number and recurrent properties"

pauliPrincipleSemanticCoordinate : AttributionReceipt
pauliPrincipleSemanticCoordinate =
  attributionReceipt
    "Wikidata community"
    "Pauli exclusion principle"
    "current semantic item"
    "unassigned"
    "Q131594"
    "semantic authority only"
    "539.7"
    "https://www.wikidata.org/wiki/Q131594"
    "Wikidata item Q131594"
    "semantic identity coordinate"
    "machine-readable coordinate for the exclusion-principle concept"

------------------------------------------------------------------------
-- Classification provenance.
-- 539.7 is used as an atomic/nuclear-physics catalogue cue; 546 as inorganic
-- chemistry / periodic-law and periodic-table cue.  These are discovery/index
-- coordinates, not mathematical evidence.

record AttributionDiscipline : Set where
  constructor attributionDiscipline
  field
    qidImpliesPrimaryAuthority : Bool
    qidImpliesPrimaryAuthorityIsFalse : qidImpliesPrimaryAuthority ≡ false

    deweyImpliesScientificTruth : Bool
    deweyImpliesScientificTruthIsFalse : deweyImpliesScientificTruth ≡ false

    doiImpliesSameObjectDASHITheory : Bool
    doiImpliesSameObjectDASHITheoryIsFalse : doiImpliesSameObjectDASHITheory ≡ false

    repoDateImpliesPublicationDate : Bool
    repoDateImpliesPublicationDateIsFalse : repoDateImpliesPublicationDate ≡ false

    sourcePresenceImpliesTypechecked : Bool
    sourcePresenceImpliesTypecheckedIsFalse : sourcePresenceImpliesTypechecked ≡ false

canonicalAttributionDiscipline : AttributionDiscipline
canonicalAttributionDiscipline =
  attributionDiscipline false refl false refl false refl false refl false refl

------------------------------------------------------------------------
-- Highest-alpha snowball order.

record AttributionSnowballFrontier : Set where
  constructor attributionSnowballFrontier
  field
    firstUnpaidHistoricalArtifact : String
    firstUnpaidLeanLineage : String
    firstUnpaidPublicationIdentity : String
    firstUnpaidPhysicalBridge : String
    acquisitionRule : String
    paymentRule : String

canonicalAttributionSnowballFrontier : AttributionSnowballFrontier
canonicalAttributionSnowballFrontier =
  attributionSnowballFrontier
    "locate the original historical MDL/exclusion filling script, exact parameter schedule, executable receipt, and artifact hash"
    "trace Base369 Lean proof source before the 2026-08-12 AgdaMirror reorganization and distinguish authored proof from later file move"
    "locate any same-object pre-PR paper, DOI, arXiv, Zenodo, release, or public manuscript receipt for the atomic constructor; otherwise retain unassigned"
    "operator-to-spectrum / scale / ionisation-energy bridge, followed by nuclear-stability and bonding validation"
    "snowball laterally across repository, archive, literature, semantic and catalogue coordinates"
    "only a dependency-satisfying receipt may promote the corresponding claim"

------------------------------------------------------------------------
-- Thin cross-owner witnesses: these imports make the chronology/provenance
-- owners part of this attribution surface without rewriting their states.

chronologyOwner : Set₁
chronologyOwner = Chronology.ChronologyReceipt

provenanceOwner : Set
provenanceOwner = Provenance.SourceReceipt
