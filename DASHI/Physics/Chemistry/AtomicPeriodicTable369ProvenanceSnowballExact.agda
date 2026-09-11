module DASHI.Physics.Chemistry.AtomicPeriodicTable369ProvenanceSnowballExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Chemistry.AtomicPeriodicTable369GenerativeExact as Atomic369

------------------------------------------------------------------------
-- Typed provenance / archaeology companion for the generative atom formalism.
--
-- The purpose is to keep historical source identity, later reconstruction,
-- current repo-native theorem ownership, and future empirical promotion
-- obligations separate.  Acquisition may snowball out of dependency order;
-- conclusion-paying promotion may not.

data SourceClass : Set where
  historicalConversationArchive : SourceClass
  historicalProgrammaticRegression : SourceClass
  currentRepoTheoremOwner : SourceClass
  currentRepoBoundaryOwner : SourceClass
  reconstructedFormalism : SourceClass
  externalPhysicalEvidence : SourceClass

data ClaimStatus : Set where
  historicalReport : ClaimStatus
  exactRepoTheorem : ClaimStatus
  structuralRegression : ClaimStatus
  reconstructedBridge : ClaimStatus
  openPhysicalObligation : ClaimStatus

data AuthorityClass : Set where
  provenanceOnly : AuthorityClass
  structuralAuthority : AuthorityClass
  regressionAuthority : AuthorityClass
  physicalAuthorityRequired : AuthorityClass

record SourceReceipt : Set where
  constructor sourceReceipt
  field
    sourceClass : SourceClass
    claimStatus : ClaimStatus
    authority : AuthorityClass
    title : String
    locator : String
    relationship : String

open SourceReceipt public

historicalAtomArchive : SourceReceipt
historicalAtomArchive =
  sourceReceipt
    historicalConversationArchive
    historicalReport
    provenanceOnly
    "DASHI Atom"
    "attached export DASHI Atom(20260911-021928).pdf; especially pages 294-301 and 418"
    "historical reconstruction source for kernel filling, MDL ordering, noble-gas-like closures, periodicity, and structure-versus-scale discussion"

historicalFiniteFillingRegression : SourceReceipt
historicalFiniteFillingRegression =
  sourceReceipt
    historicalProgrammaticRegression
    structuralRegression
    regressionAuthority
    "DASHI Atom finite MDL filling regression"
    "historical thread reports first 15+ elements and closure coordinates Z=2,10,18"
    "regression evidence for the structural constructor; not authority for spectra, ionisation energies, bonding, or complete chemistry"

currentAtomicFermionOwner : SourceReceipt
currentAtomicFermionOwner =
  sourceReceipt
    currentRepoTheoremOwner
    exactRepoTheorem
    structuralAuthority
    "DASHI.Physics.Foundations.AtomicFermionShellExact"
    "repo-native Agda owner"
    "exact owner for AtomicSpecies separation, shell/subshell capacity combinatorics, finite fermionic occupancy, interaction toy regression, and authority boundaries"

currentValenceOwner : SourceReceipt
currentValenceOwner =
  sourceReceipt
    currentRepoTheoremOwner
    exactRepoTheorem
    structuralAuthority
    "DASHI.Physics.Foundations.AtomicValenceFermionBridgeExact"
    "repo-native Agda owner"
    "exact owner for finite antisymmetric exchange, duplicate-state vanishing, and valence equivalence classes"

currentTriadicOwner : SourceReceipt
currentTriadicOwner =
  sourceReceipt
    currentRepoTheoremOwner
    exactRepoTheorem
    structuralAuthority
    "DASHI.Biology.TriadicKernelLiftQuotientExact"
    "repo-native Agda owner"
    "exact owner for ternary kernel carrier, nine-sheet lift/split equivalence, involution, and finite quotient structure"

currentRecurrenceOwner : SourceReceipt
currentRecurrenceOwner =
  sourceReceipt
    currentRepoBoundaryOwner
    exactRepoTheorem
    structuralAuthority
    "DASHI.Physics.Chemistry.AtomicShellRecurrence"
    "repo-native Agda owner"
    "owner for shell-completion recurrence and closed-shell perturbative projector-lock interface"

currentPeriodicRecoveryOwner : SourceReceipt
currentPeriodicRecoveryOwner =
  sourceReceipt
    currentRepoBoundaryOwner
    exactRepoTheorem
    structuralAuthority
    "DASHI.Physics.Chemistry.AtomicPeriodicTableRecoveryBoundary"
    "repo-native Agda owner"
    "owner for the explicit periodic-table recovery boundary and remaining bridge obligations"

currentGenerativeFormalism : SourceReceipt
currentGenerativeFormalism =
  sourceReceipt
    reconstructedFormalism
    reconstructedBridge
    structuralAuthority
    "DASHI.Physics.Chemistry.AtomicPeriodicTable369GenerativeExact"
    "this PR"
    "canonical composition of the historical atom programme with existing 369, fermion, valence, recurrence, and recovery owners"

------------------------------------------------------------------------
-- Provenance graph.

data ProvenanceEdge : SourceReceipt -> SourceReceipt -> Set where
  archiveReconstructedIntoCurrent :
    ProvenanceEdge historicalAtomArchive currentGenerativeFormalism

  finiteRegressionInformsCurrent :
    ProvenanceEdge historicalFiniteFillingRegression currentGenerativeFormalism

  triadicOwnerSuppliesSubstrate :
    ProvenanceEdge currentTriadicOwner currentGenerativeFormalism

  fermionOwnerSuppliesCapacityAndBoundary :
    ProvenanceEdge currentAtomicFermionOwner currentGenerativeFormalism

  valenceOwnerSuppliesQuotient :
    ProvenanceEdge currentValenceOwner currentGenerativeFormalism

  recurrenceOwnerSuppliesPeriodicity :
    ProvenanceEdge currentRecurrenceOwner currentGenerativeFormalism

  recoveryOwnerSuppliesPromotionBoundary :
    ProvenanceEdge currentPeriodicRecoveryOwner currentGenerativeFormalism

------------------------------------------------------------------------
-- Acquisition/payment distinction.

data EvidenceState : Set where
  located : EvidenceState
  retainedUnpaid : EvidenceState
  conclusionPaying : EvidenceState
  notLocated : EvidenceState

record SnowballTarget : Set where
  constructor snowballTarget
  field
    target : String
    state : EvidenceState
    pays : String

open SnowballTarget public

pythonFillingScript : SnowballTarget
pythonFillingScript =
  snowballTarget
    "original Python MDL filling script / exact commit or artifact hash"
    notLocated
    "historical computational identity for the reported Z=2,10,18 regression"

earliestAtomThreadTimestamp : SnowballTarget
earliestAtomThreadTimestamp =
  snowballTarget
    "earliest source object / timestamp for atoms-as-dictionaries and kernel-exhaustion formulation"
    retainedUnpaid
    "chronology and priority only; does not strengthen the mathematics"

fullShellOrderingReceipt : SnowballTarget
fullShellOrderingReceipt =
  snowballTarget
    "complete ordering rule and parameter schedule used by the historical finite filling experiment"
    notLocated
    "reproducibility of the finite structural regression beyond closure points"

physicalSpectrumBridge : SnowballTarget
physicalSpectrumBridge =
  snowballTarget
    "typed operator-to-spectrum physical bridge"
    notLocated
    "SpectrumRecovery in FullPeriodicTableRecovery"

nuclearStabilityBridge : SnowballTarget
nuclearStabilityBridge =
  snowballTarget
    "nuclear stability model/receipt indexed by Z and neutron sector"
    notLocated
    "NuclearStabilityCompatibility in FullPeriodicTableRecovery"

ionisationCalibrationBridge : SnowballTarget
ionisationCalibrationBridge =
  snowballTarget
    "physical scale calibration and ionisation-energy observable bridge"
    notLocated
    "observable quantitative chemistry beyond the structural constructor"

bondingBridge : SnowballTarget
bondingBridge =
  snowballTarget
    "molecular merge / bonding interpretation and empirical validation bridge"
    notLocated
    "chemistry beyond atomic periodicity"

------------------------------------------------------------------------
-- Snowball rule: later evidence may be retained before an earlier dependency
-- is paid, but retention alone cannot manufacture conclusion authority.

record SnowballDiscipline : Set where
  constructor snowballDiscipline
  field
    acquisitionMayBeOutOfDependencyOrder : Bool
    acquisitionMayBeOutOfDependencyOrderIsTrue :
      acquisitionMayBeOutOfDependencyOrder ≡ true

    retainedLaterEvidencePaysEarlierMissingDependency : Bool
    retainedLaterEvidencePaysEarlierMissingDependencyIsFalse :
      retainedLaterEvidencePaysEarlierMissingDependency ≡ false

    historicalReportEqualsRepoTheorem : Bool
    historicalReportEqualsRepoTheoremIsFalse :
      historicalReportEqualsRepoTheorem ≡ false

    regressionEqualsEmpiricalPhysicalAuthority : Bool
    regressionEqualsEmpiricalPhysicalAuthorityIsFalse :
      regressionEqualsEmpiricalPhysicalAuthority ≡ false

canonicalSnowballDiscipline : SnowballDiscipline
canonicalSnowballDiscipline =
  snowballDiscipline true refl false refl false refl false refl

------------------------------------------------------------------------
-- Compact dashboard for external comparison.
--
-- The historical/current DASHI claim paid here is generative structure:
--  ternary substrate -> fermionic admissibility -> shell capacity -> valence
--  quotient -> recurrence.
-- It is intentionally not identified with any particular external manifold,
-- fixed element count, or topological lookup table.

record ProvenanceDashboard : Set where
  field
    formalismOwner : SourceReceipt
    archive : SourceReceipt
    substrateOwner : SourceReceipt
    fermionOwner : SourceReceipt
    valenceOwner : SourceReceipt
    recurrenceOwner : SourceReceipt
    recoveryOwner : SourceReceipt
    snowballDisciplineReceipt : SnowballDiscipline

canonicalProvenanceDashboard : ProvenanceDashboard
canonicalProvenanceDashboard =
  record
    { formalismOwner = currentGenerativeFormalism
    ; archive = historicalAtomArchive
    ; substrateOwner = currentTriadicOwner
    ; fermionOwner = currentAtomicFermionOwner
    ; valenceOwner = currentValenceOwner
    ; recurrenceOwner = currentRecurrenceOwner
    ; recoveryOwner = currentPeriodicRecoveryOwner
    ; snowballDisciplineReceipt = canonicalSnowballDiscipline
    }

-- This type alias keeps the dashboard mechanically tied to the generative
-- owner without lifting SourceReceipt itself into a higher universe.
CanonicalFormalism : Set₁
CanonicalFormalism = Atomic369.CanonicalAtomicPeriodicTableStatement
