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
    "539.7 atom / 546.8 periodic-table topic coordinates"
    "attached conversation export; canonical archive thread id 25ec0d2e654f33ea6f524f816b4c465e86ef21cf"
    "historical source object"
    "provenance authority for what the programme reported, reconstructed, or attempted"
    "records atoms-as-dictionaries, MDL/exclusion filling, Z=2,10,18 closures, embedded code-shaped reconstructions, reported/rerun alpha-sensitivity experiments, and toy ionization work; original standalone executable/hash remains unresolved"

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

base369AgdaInception : AttributionReceipt
base369AgdaInception =
  attributionReceipt
    "Johl Brown"
    "Base369"
    "2026-02-16"
    "unassigned"
    "unassigned"
    "primary repository formal implementation receipt"
    "511 / 530 classification cue"
    "https://github.com/chboishabba/dashi_agda/blob/65266f7edc1ec7bb52e59ee020209cc5cb0eecec/Base369.agda"
    "dashi_agda init commit 65266f7edc1ec7bb52e59ee020209cc5cb0eecec; blob 8dc130c5af5a28580f729a57ea9e8ba610c0e9ad"
    "formal substrate chronology authority"
    "Base369 is present in the repository's init commit, with explicit 3/6/9 cyclic carriers, repeated rotation, order laws, identities, and ternary associativity"

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
    "539.7 / 546.8"
    "https://github.com/chboishabba/dashi_agda/commit/42e1d740141b0e9e1ca717ae5df79d6e31546c07"
    "chboishabba/dashi_agda commit 42e1d740141b0e9e1ca717ae5df79d6e31546c07"
    "implementation chronology authority"
    "earliest direct repo-native atom/chemistry closure milestone located in this audit; commit explicitly states staged closure rather than finished chemistry recovery"

leanBase369Mirror : AttributionReceipt
leanBase369Mirror =
  attributionReceipt
    "Johl Brown"
    "Lean mirror of Base369.agda"
    "2026-07-07"
    "unassigned"
    "unassigned"
    "primary repository cross-assistant proof-source receipt"
    "511 / 530 classification cue"
    "https://github.com/chboishabba/dashi_lean4/commit/55132524c2e132c0b86c17eeb60d7e39c3af08b6"
    "commit 55132524c2e132c0b86c17eeb60d7e39c3af08b6 adds Base369.lean from zero lines; moved to AgdaMirror/Base369.lean on 2026-08-12 by commit 72734285fd83387837e0025eb51a93b63629a0b9"
    "Lean proof-source authority for the finite 3/6/9 carrier laws only"
    "contains concrete proof terms for spin/modular XOR agreement, rotation orders, identities, and ternary associativity; does not mirror the atom constructor"

explicitPeriodicRecoveryBoundary : AttributionReceipt
explicitPeriodicRecoveryBoundary =
  attributionReceipt
    "Johl Brown"
    "atomic periodic-table recovery boundary"
    "2026-07-19"
    "unassigned"
    "periodic table Q10693"
    "primary repository formal implementation receipt"
    "546.8"
    "https://github.com/chboishabba/dashi_agda/commit/554e8f930dfee5293d75d3bb67be8098bde088d3"
    "chboishabba/dashi_agda commit 554e8f930dfee5293d75d3bb67be8098bde088d3; PR #101"
    "formal recovery-boundary authority"
    "explicit shell-recurrence / periodic-table recovery owner; physical completion remains fail-closed"

currentAtomicManuscript : AttributionReceipt
currentAtomicManuscript =
  attributionReceipt
    "Johl Brown / DASHI"
    "DASHI Atomic and Periodic-Table Formalism: Kernel Filling, MDL Selection, Valence Recurrence, and Provenance Gates"
    "2026-09-11"
    "unassigned; same-object DOI not yet located"
    "atom Q9121; periodic table Q10693; Pauli exclusion principle Q131594"
    "primary repository manuscript for the current consolidation"
    "539.7 / 546.8"
    "https://github.com/chboishabba/dashi_agda/pull/886"
    "Docs/papers/drafts/DASHIAtomicPeriodicTable369Formalism.tex on PR #886"
    "manuscript/provenance authority; not peer-review or empirical authority"
    "current paper-facing consolidation of the recovered constructor and its non-promotion boundaries"

------------------------------------------------------------------------
-- External primary / semantic anchors.

ibrahim2017 : AttributionReceipt
ibrahim2017 =
  attributionReceipt
    "Mark Ibrahim; Christopher M. Danforth; Peter Sheridan Dodds"
    "Connecting every bit of knowledge: The structure of Wikipedia's First Link Network"
    "2017"
    "10.1016/j.jocs.2016.12.001"
    "unassigned"
    "primary source for the first-link/traversal-funnel search policy; not atomic-physics authority"
    "unresolved for the publication object"
    "https://doi.org/10.1016/j.jocs.2016.12.001"
    "Journal of Computational Science 19 (2017), 21-30; arXiv:1605.00309"
    "search-policy / network-method authority"
    "donor for deterministic traversal from specific to typed explanatory parents; does not promote Dewey/QID adjacency into theorem implication"

pauli1925 : AttributionReceipt
pauli1925 =
  attributionReceipt
    "Wolfgang Pauli"
    "Ueber den Zusammenhang des Abschlusses der Elektronengruppen im Atom mit der Komplexstruktur der Spektren"
    "1925"
    "10.1007/BF02980631"
    "Pauli exclusion principle Q131594"
    "primary historical physics paper"
    "539.7 topic coordinate; publication-specific Dewey unresolved"
    "https://doi.org/10.1007/BF02980631"
    "Zeitschrift fuer Physik 31, 765-783"
    "primary scientific authority for the historical exclusion-principle source object"
    "external anchor for hard fermionic exclusion; citation does not identify DASHI's MDL cost with physical energy"

hartree1928 : AttributionReceipt
hartree1928 =
  attributionReceipt
    "D. R. Hartree"
    "The Wave Mechanics of an Atom with a Non-Coulomb Central Field. Part II. Some Results and Discussion"
    "1928"
    "10.1017/S0305004100011920"
    "unassigned publication QID"
    "primary historical self-consistent-field atomic-structure paper"
    "publication-specific Dewey unresolved; graph topics include atom 539.7, atomic orbital 541.28, quantum mechanics 530.12"
    "https://doi.org/10.1017/S0305004100011920"
    "Mathematical Proceedings of the Cambridge Philosophical Society 24(1), 111-132"
    "primary scientific authority for Hartree's self-consistent-field method applied to atoms"
    "external method source for the open operator-to-spectrum/scale lane; does not pay the DASHI same-object realization"

slater1928 : AttributionReceipt
slater1928 =
  attributionReceipt
    "J. C. Slater"
    "The Self Consistent Field and the Structure of Atoms"
    "1928"
    "10.1103/PhysRev.32.339"
    "unassigned publication QID"
    "primary historical atomic-structure / self-consistent-field paper"
    "publication-specific Dewey unresolved; graph topics include atom 539.7, atomic orbital 541.28, quantum mechanics 530.12"
    "https://doi.org/10.1103/PhysRev.32.339"
    "Physical Review 32, 339-348"
    "primary scientific authority for analysis of Hartree self-consistent fields against the Schroedinger equation"
    "external method source for the physical spectral bridge; not a proof that the DASHI carrier realizes Hartree-Fock"

atomSemanticCoordinate : AttributionReceipt
atomSemanticCoordinate =
  attributionReceipt
    "Wikidata community"
    "atom"
    "current semantic item"
    "unassigned"
    "Q9121"
    "semantic authority only; not primary physics evidence"
    "539.7"
    "https://www.wikidata.org/wiki/Q9121"
    "Wikidata item Q9121"
    "semantic identity/catalogue coordinate"
    "machine-readable coordinate for the concept atom"

chemicalElementSemanticCoordinate : AttributionReceipt
chemicalElementSemanticCoordinate =
  attributionReceipt
    "Wikidata community"
    "chemical element"
    "current semantic item"
    "unassigned"
    "Q11344"
    "semantic authority only"
    "546"
    "https://www.wikidata.org/wiki/Q11344"
    "Wikidata item Q11344; IUPAC Gold Book C01022"
    "semantic identity/catalogue coordinate"
    "machine-readable coordinate for chemical elements; distinct from the periodic-table object"

periodicTableSemanticCoordinate : AttributionReceipt
periodicTableSemanticCoordinate =
  attributionReceipt
    "Wikidata community"
    "periodic table"
    "current semantic item"
    "unassigned"
    "Q10693"
    "semantic authority only; not primary chemistry evidence"
    "546.8"
    "https://www.wikidata.org/wiki/Q10693"
    "Wikidata item Q10693"
    "semantic identity/catalogue coordinate"
    "machine-readable coordinate for the periodic-table concept; Wikidata records chemical element Q11344 as the items classified"

atomicOrbitalSemanticCoordinate : AttributionReceipt
atomicOrbitalSemanticCoordinate =
  attributionReceipt
    "Wikidata community"
    "atomic orbital"
    "current semantic item"
    "unassigned"
    "Q53860"
    "semantic authority only"
    "541.28"
    "https://www.wikidata.org/wiki/Q53860"
    "Wikidata item Q53860; IUPAC Gold Book A00500"
    "semantic identity/catalogue coordinate"
    "external representation coordinate for the one-particle orbital layer"

quantumMechanicsSemanticCoordinate : AttributionReceipt
quantumMechanicsSemanticCoordinate =
  attributionReceipt
    "Wikidata community"
    "quantum mechanics"
    "current semantic item"
    "unassigned"
    "Q944"
    "semantic authority only"
    "530.12"
    "https://www.wikidata.org/wiki/Q944"
    "Wikidata item Q944"
    "semantic identity/catalogue coordinate"
    "external theory coordinate for the physical orbital/spectral semantics"

carbonSemanticCoordinate : AttributionReceipt
carbonSemanticCoordinate =
  attributionReceipt
    "Wikidata community"
    "carbon"
    "current semantic item"
    "unassigned"
    "Q623"
    "semantic authority only"
    "547"
    "https://www.wikidata.org/wiki/Q623"
    "Wikidata item Q623; IUPAC Gold Book C00821"
    "semantic identity/catalogue coordinate"
    "downstream chemistry branch used by the historical dashiQ carbon-suitability programme"

ionizationEnergySemanticCoordinate : AttributionReceipt
ionizationEnergySemanticCoordinate =
  attributionReceipt
    "Wikidata / IUPAC semantic sources"
    "ionization energy"
    "current semantic item"
    "unassigned"
    "Q483769"
    "semantic/quantity authority only"
    "unresolved in the inspected Wikidata item"
    "https://www.wikidata.org/wiki/Q483769"
    "Wikidata Q483769; IUPAC Gold Book I03199; IEV 113-06-39"
    "semantic identity / quantity coordinate"
    "first quantitative validation target after structural shell recovery; Dewey is retained unresolved rather than inferred from neighbours"

hartreeFockSemanticCoordinate : AttributionReceipt
hartreeFockSemanticCoordinate =
  attributionReceipt
    "Wikidata community"
    "Hartree-Fock method"
    "current semantic item"
    "unassigned"
    "Q7879841"
    "semantic authority only"
    "unresolved in the inspected Wikidata item"
    "https://www.wikidata.org/wiki/Q7879841"
    "Wikidata item Q7879841"
    "semantic identity coordinate"
    "external method coordinate for the open self-consistent operator/spectrum bridge"

pauliPrincipleSemanticCoordinate : AttributionReceipt
pauliPrincipleSemanticCoordinate =
  attributionReceipt
    "Wikidata community"
    "Pauli exclusion principle"
    "current semantic item"
    "unassigned"
    "Q131594"
    "semantic authority only"
    "539.7 topic coordinate"
    "https://www.wikidata.org/wiki/Q131594"
    "Wikidata item Q131594"
    "semantic identity coordinate"
    "machine-readable coordinate for the exclusion-principle concept"

------------------------------------------------------------------------
-- Classification provenance.
-- The inspected semantic graph gives the following exact catalogue
-- coordinates: periodic table 546.8; chemical element 546; atom 539.7;
-- atomic orbital 541.28; quantum mechanics 530.12; carbon 547.  Ionization
-- energy and Hartree-Fock method have no Dewey field in the inspected items,
-- so they remain unresolved. These are navigation/index coordinates only.

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
    "the DASHI Atom archive now pays embedded code-shaped reconstruction, run narrative, n+alpha*l cost, Z=2/10/18 closure reports, alpha-sensitivity and toy ionization work; still locate the original standalone MDL/exclusion script, exact original parameter schedule, executable receipt, and artifact hash"
    "paid to 2026-07-07 commit 55132524c2e132c0b86c17eeb60d7e39c3af08b6, which adds Base369.lean from zero lines; any earlier off-repository Aristotle artifact remains a distinct provenance question"
    "locate any same-object pre-PR paper, DOI, arXiv, Zenodo, release, or public manuscript receipt for the atomic constructor; otherwise retain unassigned"
    "Hartree/Slater primary self-consistent-field method sources are acquired; the unpaid leaf is the same-object DASHI operator-to-spectrum / calibrated ionisation-energy bridge, followed by nuclear-stability and bonding validation"
    "snowball through typed Ibrahim first-link parents plus DOI, QID, Dewey, Gold Book, repository and archive coordinates; evidence may be retained out of payment order"
    "only a dependency-satisfying same-object/source receipt may promote the corresponding conclusion"

------------------------------------------------------------------------
-- Thin cross-owner witnesses: these imports make the chronology/provenance
-- owners part of this attribution surface without rewriting their states.

chronologyOwner : Set₁
chronologyOwner = Chronology.ChronologyReceipt

provenanceOwner : Set
provenanceOwner = Provenance.SourceReceipt
