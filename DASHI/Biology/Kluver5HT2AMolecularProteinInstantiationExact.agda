module DASHI.Biology.Kluver5HT2AMolecularProteinInstantiationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Biology.KluverLogPolar5HT2ASourceAtlasExact as Sources
import DASHI.Biology.Kluver5HT2ACrossScaleHyperfibreExact as Hyper
import DASHI.Biology.NeurochemicalAtomicChemistryBridge as AtomicChem
import DASHI.Biology.NeurochemicalProteinTargetBridge as ProteinTarget

------------------------------------------------------------------------
-- CONCRETE MOLECULAR / PROTEIN INSTANTIATION
--
-- This fills the previously generic middle of the 5-HT2A hyperfibre with
-- recoverable molecular identities and structural receptor evidence.
--
-- External source data:
--   serotonin  : PubChem CID 5202, C10H12N2O
--   LSD        : PubChem CID 5761, C20H25N3O
--   ketanserin : PubChem CID 3822, C22H22FN3O3
--   5-HT2A/LSD receptor structures: Kim et al. 2020; Gumpper et al. 2025;
--                                  PDB 9AS4.
--
-- DASHI extension:
-- the records and cross-scale role partition below are repo-native.  Molecular
-- identity does not import affinity, efficacy, occupancy, signaling, circuit,
-- phenomenology, clinical, or dose-response authority.
------------------------------------------------------------------------

sourceAtlas : Source.AttributedSourceAtlas
sourceAtlas = Sources.canonicalKluverLogPolar5HT2AAtlas

data MolecularRole : Set where
  endogenousLigandRole : MolecularRole
  psychedelicLigandRole : MolecularRole
  antagonistProbeRole : MolecularRole

record MolecularIdentityReceipt : Set where
  constructor molecularIdentityReceipt
  field
    commonName : String
    stableIdentifier : String
    molecularFormula : String
    role : MolecularRole
    source : Source.AttributedSource

    identityOnly : Bool
    identityOnlyIsTrue : identityOnly ≡ true

    affinityImported : Bool
    affinityImportedIsFalse : affinityImported ≡ false

    efficacyImported : Bool
    efficacyImportedIsFalse : efficacyImported ≡ false

    doseResponseImported : Bool
    doseResponseImportedIsFalse : doseResponseImported ≡ false

open MolecularIdentityReceipt public

serotoninIdentity : MolecularIdentityReceipt
serotoninIdentity =
  molecularIdentityReceipt
    "serotonin / 5-hydroxytryptamine"
    "PubChem CID 5202"
    "C10H12N2O"
    endogenousLigandRole
    Sources.pubChemSerotonin
    true refl
    false refl
    false refl
    false refl

lsdIdentity : MolecularIdentityReceipt
lsdIdentity =
  molecularIdentityReceipt
    "lysergic acid diethylamide / lysergide"
    "PubChem CID 5761"
    "C20H25N3O"
    psychedelicLigandRole
    Sources.pubChemLSD
    true refl
    false refl
    false refl
    false refl

ketanserinIdentity : MolecularIdentityReceipt
ketanserinIdentity =
  molecularIdentityReceipt
    "ketanserin"
    "PubChem CID 3822"
    "C22H22FN3O3"
    antagonistProbeRole
    Sources.pubChemKetanserin
    true refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Receptor structural evidence.
------------------------------------------------------------------------

data ReceptorStructureEvidenceKind : Set where
  direct5HT2AStructure : ReceptorStructureEvidenceKind
  comparative5HT2AStructureSet : ReceptorStructureEvidenceKind
  neighboring5HT2BStructuralKineticEvidence : ReceptorStructureEvidenceKind
  deposited5HT2AComplex : ReceptorStructureEvidenceKind

record ReceptorStructureReceipt : Set where
  constructor receptorStructureReceipt
  field
    receptor : String
    ligand : String
    evidenceKind : ReceptorStructureEvidenceKind
    source : Source.AttributedSource
    structureIdentifier : String
    importedReading : String

    directInVivoBrainState : Bool
    directInVivoBrainStateIsFalse :
      directInVivoBrainState ≡ false

    phenomenologyRecovered : Bool
    phenomenologyRecoveredIsFalse :
      phenomenologyRecovered ≡ false

open ReceptorStructureReceipt public

kim5HT2ALSDStructure : ReceptorStructureReceipt
kim5HT2ALSDStructure =
  receptorStructureReceipt
    "human 5-HT2A receptor"
    "LSD"
    direct5HT2AStructure
    Sources.kimEtAl2020
    "Cell 2020 structural result"
    "direct 5-HT2A structural evidence under hallucinogen/Gq-coupled structural conditions"
    false refl
    false refl

gumpper5HT2AComparativeStructures : ReceptorStructureReceipt
gumpper5HT2AComparativeStructures =
  receptorStructureReceipt
    "human 5-HT2A receptor"
    "5-HT, LSD, psilocin, DMT, mescaline, BOL and comparison ligands"
    comparative5HT2AStructureSet
    Sources.gumpperEtAl2025
    "Nature Communications 2025 comparative cryo-EM set"
    "ligand-dependent active-state receptor structures support a many-ligand receptor-state comparison surface"
    false refl
    false refl

wacker5HT2BNeighborEvidence : ReceptorStructureReceipt
wacker5HT2BNeighborEvidence =
  receptorStructureReceipt
    "human 5-HT2B structure with 5-HT2A kinetic observations"
    "LSD"
    neighboring5HT2BStructuralKineticEvidence
    Sources.wackerEtAl2017
    "Cell 2017"
    "the crystal structure is 5-HT2B, not 5-HT2A; 5-HT2A enters through kinetic/signaling observations and must remain a separate source role"
    false refl
    false refl

pdb9AS4Receipt : ReceptorStructureReceipt
pdb9AS4Receipt =
  receptorStructureReceipt
    "human 5-HT2A receptor"
    "LSD"
    deposited5HT2AComplex
    Sources.pdb9AS4
    "PDB 9AS4 / DOI 10.2210/pdb9AS4/pdb"
    "recoverable cryo-EM complex identifier for LSD-bound 5-HT2A with mini-Gq and scFv16"
    false refl
    false refl

canonicalReceptorStructureReceipts : List ReceptorStructureReceipt
canonicalReceptorStructureReceipts =
  kim5HT2ALSDStructure
  ∷ gumpper5HT2AComparativeStructures
  ∷ wacker5HT2BNeighborEvidence
  ∷ pdb9AS4Receipt
  ∷ []

------------------------------------------------------------------------
-- Concrete reuse of existing chemistry/protein slots.
------------------------------------------------------------------------

atomicChemistrySlots : List AtomicChem.NeurochemicalAtomicChemistrySlot
atomicChemistrySlots =
  AtomicChem.canonicalNeurochemicalAtomicChemistrySlots

proteinTargetKinds : List ProteinTarget.ProteinTargetContextKind
proteinTargetKinds =
  ProteinTarget.canonicalProteinTargetContextKinds

proteinActionCandidates : List ProteinTarget.ProteinTargetActionCandidate
proteinActionCandidates =
  ProteinTarget.canonicalProteinTargetActionCandidates

record FiveHT2AMolecularProteinInstantiation : Set₁ where
  constructor fiveHT2AMolecularProteinInstantiation
  field
    hyperfibre : Hyper.Kluver5HT2ACrossScaleHyperfibre

    serotonin : MolecularIdentityReceipt
    lsd : MolecularIdentityReceipt
    ketanserin : MolecularIdentityReceipt

    receptorStructures : List ReceptorStructureReceipt

    chemistrySlots :
      List AtomicChem.NeurochemicalAtomicChemistrySlot

    proteinTargets :
      List ProteinTarget.ProteinTargetContextKind

    proteinActions :
      List ProteinTarget.ProteinTargetActionCandidate

    molecularIdentityNowConcrete : Bool
    molecularIdentityNowConcreteIsTrue :
      molecularIdentityNowConcrete ≡ true

    receptorStructureEvidenceNowConcrete : Bool
    receptorStructureEvidenceNowConcreteIsTrue :
      receptorStructureEvidenceNowConcrete ≡ true

    assayBoundAffinityStillMissing : Bool
    assayBoundAffinityStillMissingIsTrue :
      assayBoundAffinityStillMissing ≡ true

    concentrationOccupancyTransferStillMissing : Bool
    concentrationOccupancyTransferStillMissingIsTrue :
      concentrationOccupancyTransferStillMissing ≡ true

    signalingBiasToCircuitTransferStillMissing : Bool
    signalingBiasToCircuitTransferStillMissingIsTrue :
      signalingBiasToCircuitTransferStillMissing ≡ true

    receptorStateToKluverModeTransferStillMissing : Bool
    receptorStateToKluverModeTransferStillMissingIsTrue :
      receptorStateToKluverModeTransferStillMissing ≡ true

open FiveHT2AMolecularProteinInstantiation public

canonicalFiveHT2AMolecularProteinInstantiation :
  FiveHT2AMolecularProteinInstantiation
canonicalFiveHT2AMolecularProteinInstantiation =
  fiveHT2AMolecularProteinInstantiation
    Hyper.canonicalKluver5HT2ACrossScaleHyperfibre
    serotoninIdentity
    lsdIdentity
    ketanserinIdentity
    canonicalReceptorStructureReceipts
    atomicChemistrySlots
    proteinTargetKinds
    proteinActionCandidates
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl

------------------------------------------------------------------------
-- Exact source-boundary / anti-collapse results.
------------------------------------------------------------------------

data MolecularFormulaDeterminesAffinity : Set where

data StructureDeterminesPhenomenology : Set where

data KetanserinIdentityAloneProvesSelective5HT2ABlockade : Set where

molecularFormulaDoesNotDetermineAffinity :
  MolecularFormulaDeterminesAffinity → ⊥
molecularFormulaDoesNotDetermineAffinity ()

structureDoesNotDeterminePhenomenology :
  StructureDeterminesPhenomenology → ⊥
structureDoesNotDeterminePhenomenology ()

ketanserinIdentityAloneDoesNotProveSelective5HT2ABlockade :
  KetanserinIdentityAloneProvesSelective5HT2ABlockade → ⊥
ketanserinIdentityAloneDoesNotProveSelective5HT2ABlockade ()
