module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseConformationalEmpiricalExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Equality using (_≡_; refl; sym; trans)

import DASHI.Physics.Chemistry.AtomicPeriodicTable369ProteinBackboneStereochemistryExact as Backbone
import DASHI.Biology.Protein.ProteinConformationAttractor as Conformation
import DASHI.Biology.Protein.ProteinFunctionProjection as Function

------------------------------------------------------------------------
-- SAME-SEQUENCE EXPERIMENTAL PROTEIN CONFORMATION PAIR: E. COLI ADENYLATE KINASE
--
-- RCSB / primary-source pair:
--   4AKE : unligated open E. coli adenylate kinase, 2.20 A X-ray structure.
--   1AKE : Ap5A-bound closed E. coli adenylate kinase, 1.90 A X-ray structure.
--
-- Muller et al. 1996 explicitly describe the comparison as two very different
-- conformations of the same polypeptide chain.  The pair therefore pays the
-- protein-scale version of the repo's same-coarse separating-pair pattern:
--
--   same primary sequence
--      + different environment / ligand context
--      + different resolved 3-D conformation.
--
-- It does not prove that ligand context uniquely determines conformation, that
-- every catalytic state is represented by either crystal, or that two crystal
-- structures constitute a complete folding / catalytic mechanism.
------------------------------------------------------------------------

data AdKPrimarySequence : Set where
  eColiAdKSequence : AdKPrimarySequence

data AdKEnvironment : Set where
  unligatedContext : AdKEnvironment
  ap5aBoundContext : AdKEnvironment

data AdKConformation : Set where
  openConformation : AdKConformation
  closedConformation : AdKConformation

data AdKResolvedState : Set where
  pdb4AKEState : AdKResolvedState
  pdb1AKEState : AdKResolvedState

primarySequence : AdKResolvedState → AdKPrimarySequence
primarySequence pdb4AKEState = eColiAdKSequence
primarySequence pdb1AKEState = eColiAdKSequence

environment : AdKResolvedState → AdKEnvironment
environment pdb4AKEState = unligatedContext
environment pdb1AKEState = ap5aBoundContext

conformation : AdKResolvedState → AdKConformation
conformation pdb4AKEState = openConformation
conformation pdb1AKEState = closedConformation

samePrimarySequence :
  primarySequence pdb4AKEState ≡ primarySequence pdb1AKEState
samePrimarySequence = refl

environmentsDiffer :
  environment pdb4AKEState ≡ environment pdb1AKEState → ⊥
environmentsDiffer ()

conformationsDiffer :
  conformation pdb4AKEState ≡ conformation pdb1AKEState → ⊥
conformationsDiffer ()

record SequenceOnlyConformationFactor : Set where
  constructor sequenceOnlyConformationFactor
  field
    factor : AdKPrimarySequence → AdKConformation
    law : (x : AdKResolvedState) → conformation x ≡ factor (primarySequence x)

open SequenceOnlyConformationFactor public

conformationDoesNotFactorThroughSequenceAlone :
  SequenceOnlyConformationFactor → ⊥
conformationDoesNotFactorThroughSequenceAlone F =
  conformationsDiffer
    (trans
      (law F pdb4AKEState)
      (sym (law F pdb1AKEState)))

-- In this finite empirical fixture, adding the observed environment coordinate
-- is enough to distinguish the two resolved states.  This is not promoted to a
-- universal deterministic environment -> conformation law.
stateFromEnvironment : AdKEnvironment → AdKConformation
stateFromEnvironment unligatedContext = openConformation
stateFromEnvironment ap5aBoundContext = closedConformation

environmentPaysFixture :
  (x : AdKResolvedState) →
  conformation x ≡ stateFromEnvironment (environment x)
environmentPaysFixture pdb4AKEState = refl
environmentPaysFixture pdb1AKEState = refl

------------------------------------------------------------------------
-- Reuse existing downstream carriers rather than replacing protein ontology.
------------------------------------------------------------------------

backboneStereochemistrySurface : Set
backboneStereochemistrySurface = Backbone.BackboneRichState

proteinConformationSystemSurface : Set₁
proteinConformationSystemSurface = Conformation.ProteinConformationSystem

proteinMultipleAttractorSurface :
  Conformation.ProteinConformationSystem → Set₁
proteinMultipleAttractorSurface = Conformation.MultipleAttractorWitness

proteinFunctionSystemSurface : Set₁
proteinFunctionSystemSurface = Function.ProteinFunctionSystem

------------------------------------------------------------------------
-- Snowball attribution.  DOI / PDB / QID / UniProt / Dewey / OEIS remain
-- typed navigation / authority coordinates and do not import a theorem.
------------------------------------------------------------------------

record AdKSourceCoordinate : Set where
  constructor adkSourceCoordinate
  field
    label : String
    doi : String
    pdb : String
    qid : String
    uniprot : String
    dewey : String
    oeis : String
    primaryStatus : String
    directLink : String
    sourceRole : String

open4AKE : AdKSourceCoordinate
open4AKE =
  adkSourceCoordinate
    "E. coli adenylate kinase open unligated structure"
    "10.2210/pdb4AKE/pdb"
    "4AKE"
    "enzyme-class Q356240; exact PDB-object QID unresolved"
    "P69441"
    "exact structure-entry Dewey unresolved"
    "not an integer-sequence object; no same-object OEIS coordinate"
    "primary experimental PDB structure; associated primary research article"
    "https://www.rcsb.org/structure/4AKE"
    "2.20 A X-ray structure; RCSB reports no mutation; substrate-free/open structural endpoint"

closed1AKE : AdKSourceCoordinate
closed1AKE =
  adkSourceCoordinate
    "E. coli adenylate kinase Ap5A-bound closed structure"
    "10.2210/pdb1AKE/pdb"
    "1AKE"
    "enzyme-class Q356240; exact PDB-object QID unresolved"
    "P69441"
    "exact structure-entry Dewey unresolved"
    "not an integer-sequence object; no same-object OEIS coordinate"
    "primary experimental PDB structure; associated primary research article"
    "https://www.rcsb.org/structure/1AKE"
    "1.90 A X-ray inhibitor-bound structure; closed endpoint / transition-state-model context"

muller1996SameChain : AdKSourceCoordinate
muller1996SameChain =
  adkSourceCoordinate
    "Muller et al. 1996, Adenylate kinase motions during catalysis"
    "10.1016/S0969-2126(96)00018-4"
    "4AKE primary citation; compares 4AKE with 1AKE"
    "source-article QID unresolved"
    "P69441"
    "exact article-level Dewey unresolved"
    "not an integer-sequence object"
    "primary structural research article"
    "https://doi.org/10.1016/S0969-2126(96)00018-4"
    "explicit same-polypeptide-chain open/closed comparison and catalytic-cycle conformational interpretation"

mullerSchulz1992Closed : AdKSourceCoordinate
mullerSchulz1992Closed =
  adkSourceCoordinate
    "Muller and Schulz 1992, E. coli adenylate kinase-Ap5A complex"
    "10.1016/0022-2836(92)90582-5"
    "1AKE"
    "source-article QID unresolved"
    "P69441"
    "exact article-level Dewey unresolved"
    "not an integer-sequence object"
    "primary structural research article"
    "https://doi.org/10.1016/0022-2836(92)90582-5"
    "primary 1AKE closed inhibitor-bound structure; model for a catalytic transition-state geometry"

uniprotAdK : AdKSourceCoordinate
uniprotAdK =
  adkSourceCoordinate
    "E. coli K-12 adenylate kinase protein identity"
    "not a publication DOI"
    "PDB cross-references include adenylate-kinase structures"
    "enzyme-class Q356240"
    "P69441"
    "exact protein-item Dewey unresolved"
    "not an integer-sequence object"
    "reviewed UniProtKB / Swiss-Prot protein identity source"
    "https://www.uniprot.org/uniprotkb/P69441"
    "same-protein identity coordinate: adk, E. coli K-12, 214 aa"

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

record AdenylateKinaseEmpiricalBoundary : Set where
  constructor adenylateKinaseEmpiricalBoundary
  field
    samePolypeptideSequence : Bool
    samePolypeptideSequenceIsTrue : samePolypeptideSequence ≡ true

    openClosedStructuralPairPaid : Bool
    openClosedStructuralPairPaidIsTrue : openClosedStructuralPairPaid ≡ true

    conformationFactorsThroughSequenceAlone : Bool
    conformationFactorsThroughSequenceAloneIsFalse :
      conformationFactorsThroughSequenceAlone ≡ false

    environmentContextRequired : Bool
    environmentContextRequiredIsTrue : environmentContextRequired ≡ true

    pdbIdentityImportsDynamicsMechanism : Bool
    pdbIdentityImportsDynamicsMechanismIsFalse :
      pdbIdentityImportsDynamicsMechanism ≡ false

    ap5aClosedCrystalEqualsUniversalCatalyticTransitionState : Bool
    ap5aClosedCrystalEqualsUniversalCatalyticTransitionStateIsFalse :
      ap5aClosedCrystalEqualsUniversalCatalyticTransitionState ≡ false

    twoPDBEntriesProveUniversalFoldingMechanism : Bool
    twoPDBEntriesProveUniversalFoldingMechanismIsFalse :
      twoPDBEntriesProveUniversalFoldingMechanism ≡ false

canonicalAdenylateKinaseEmpiricalBoundary : AdenylateKinaseEmpiricalBoundary
canonicalAdenylateKinaseEmpiricalBoundary =
  adenylateKinaseEmpiricalBoundary
    true refl
    true refl
    false refl
    true refl
    false refl
    false refl
    false refl
