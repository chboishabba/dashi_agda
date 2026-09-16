module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseGammaCrystalReferenceAcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSparseCalibrationFibreExact as Sparse

------------------------------------------------------------------------
-- GAMMA-NEAR CRYSTAL-REFERENCE ACQUISITION
--
-- Li, Liu & Ji 2015 state that PDB 1AK2 and 2AK2 lie near the gamma state in
-- their ligand-free Figure-5 theta1/theta2 landscape and use them as empirical
-- crystal-structure points supporting the alpha<->beta<->gamma route endpoint.
--
-- RCSB and the primary Schlauderer & Schulz 1996 paper pay a different source
-- role for the same PDB objects: bovine mitochondrial adenylate kinase isoenzyme
-- 2, unligated, described there as an "open" conformation.  DASHI retains both
-- role statements rather than rewriting one into the other.
--
-- Therefore:
--   same PDB object across sources = paid,
--   near-gamma under Li-Liu-Ji's projection = paid,
--   open under the primary structural paper's classification = paid,
-- but PDB object = gamma state, E. coli same-sequence identity, or source
-- contradiction are NOT paid.
------------------------------------------------------------------------

liLiuJiSource : Attribution.AttributedSource
liLiuJiSource = Sparse.liLiuJi2015Source

liLiuJiReceipt : Snowball.SourceRoleSnowballReceipt liLiuJiSource
liLiuJiReceipt = Snowball.canonicalSourceRoleSnowballReceipt liLiuJiSource

schlaudererSchulz1996 : Attribution.AttributedSource
schlaudererSchulz1996 =
  Attribution.mkDOISource
    "Schlauderer and Schulz"
    "The structure of bovine mitochondrial adenylate kinase: comparison with isoenzymes in other compartments"
    "Protein Science"
    "1996"
    "10.1002/pro.5560050304"
    "https://pubmed.ncbi.nlm.nih.gov/8868479/"
    Attribution.academicArticleSource
    "pays primary structural description of 1AK2/2AK2 as unligated bovine mitochondrial adenylate kinase isoenzyme-2 crystal forms and describes both as open conformations; it does not pay Li-Liu-Ji gamma-state identity"
    Attribution.publicAttribution

schlaudererReceipt : Snowball.SourceRoleSnowballReceipt schlaudererSchulz1996
schlaudererReceipt = Snowball.canonicalSourceRoleSnowballReceipt schlaudererSchulz1996

pdb1AK2Source : Attribution.AttributedSource
pdb1AK2Source =
  Attribution.mkDOISource
    "Schlauderer and Schulz / wwPDB"
    "PDB 1AK2: adenylate kinase isoenzyme-2"
    "Protein Data Bank"
    "1996"
    "10.2210/pdb1AK2/pdb"
    "https://www.rcsb.org/structure/1AK2"
    Attribution.empiricalDatasetSource
    "pays stable deposition identity, organism, mutation status, X-ray method, 1.92 A resolution and UniProt cross-reference P08166; it does not pay gamma-state identity"
    Attribution.publicAttribution

pdb2AK2Source : Attribution.AttributedSource
pdb2AK2Source =
  Attribution.mkDOISource
    "Schlauderer and Schulz / wwPDB"
    "PDB 2AK2: adenylate kinase isoenzyme-2"
    "Protein Data Bank"
    "1996"
    "10.2210/pdb2AK2/pdb"
    "https://www.rcsb.org/structure/2AK2"
    Attribution.empiricalDatasetSource
    "pays stable deposition identity, organism, mutation status, X-ray method, 2.10 A resolution and UniProt cross-reference P08166; it does not pay gamma-state identity"
    Attribution.publicAttribution

pdb1AK2Receipt : Snowball.SourceRoleSnowballReceipt pdb1AK2Source
pdb1AK2Receipt = Snowball.canonicalSourceRoleSnowballReceipt pdb1AK2Source

pdb2AK2Receipt : Snowball.SourceRoleSnowballReceipt pdb2AK2Source
pdb2AK2Receipt = Snowball.canonicalSourceRoleSnowballReceipt pdb2AK2Source

------------------------------------------------------------------------
-- External identity coordinates.
------------------------------------------------------------------------

oneAK2PdbIdentity : Identity.ExternalIdentityDemand
oneAK2PdbIdentity = Identity.mkOptionalIdentityDemand
  "AdK gamma crystal-reference acquisition"
  "PDB 1AK2 deposition identity"
  "adenylate kinase isoenzyme-2"
  Identity.officialIdentifier
  (Identity.verified "Protein Data Bank" "1AK2")

twoAK2PdbIdentity : Identity.ExternalIdentityDemand
twoAK2PdbIdentity = Identity.mkOptionalIdentityDemand
  "AdK gamma crystal-reference acquisition"
  "PDB 2AK2 deposition identity"
  "adenylate kinase isoenzyme-2"
  Identity.officialIdentifier
  (Identity.verified "Protein Data Bank" "2AK2")

bovineAdKUniProt : Identity.ExternalIdentityDemand
bovineAdKUniProt = Identity.mkOptionalIdentityDemand
  "AdK gamma crystal-reference acquisition"
  "bovine adenylate kinase isoenzyme-2 UniProt identity"
  "AK2_BOVIN"
  Identity.officialIdentifier
  (Identity.verified "UniProt via RCSB" "P08166")

primaryArticlePmid : Identity.ExternalIdentityDemand
primaryArticlePmid = Identity.mkOptionalIdentityDemand
  "AdK gamma crystal-reference acquisition"
  "Schlauderer-Schulz 1996 PubMed identity"
  "The structure of bovine mitochondrial adenylate kinase"
  Identity.officialIdentifier
  (Identity.verified "PubMed" "8868479")

primaryArticleQid : Identity.ExternalIdentityDemand
primaryArticleQid = Identity.mkOptionalIdentityDemand
  "AdK gamma crystal-reference acquisition"
  "Schlauderer-Schulz 1996 article Wikidata identity"
  "The structure of bovine mitochondrial adenylate kinase"
  Identity.wikidataQid
  (Identity.unresolved "article-level QID unresolved in inspected sources")

oneAK2ObjectQid : Identity.ExternalIdentityDemand
oneAK2ObjectQid = Identity.mkOptionalIdentityDemand
  "AdK gamma crystal-reference acquisition"
  "PDB 1AK2 object Wikidata identity"
  "1AK2"
  Identity.wikidataQid
  (Identity.unresolved "exact PDB-object QID unresolved")

twoAK2ObjectQid : Identity.ExternalIdentityDemand
twoAK2ObjectQid = Identity.mkOptionalIdentityDemand
  "AdK gamma crystal-reference acquisition"
  "PDB 2AK2 object Wikidata identity"
  "2AK2"
  Identity.wikidataQid
  (Identity.unresolved "exact PDB-object QID unresolved")

------------------------------------------------------------------------
-- Role-sensitive same-object references.
------------------------------------------------------------------------

data SourceClassificationRole : Set where
  nearGammaInLiLandscape : SourceClassificationRole
  openInPrimaryStructuralPaper : SourceClassificationRole

record GammaCrystalReference : Set where
  constructor gamma-crystal-reference
  field
    pdbId : String
    pdbDoi : String
    organism : String
    uniprot : String
    xrayResolutionHundredthsAngstrom : Nat
    liLandscapeRole : SourceClassificationRole
    primaryPaperRole : SourceClassificationRole
    liLocator : String
    structuralLocator : String
    samePdbObjectAcrossSourcesPaid : Bool
    exactGammaStateIdentityPaid : Bool
    sameSequenceAsEcoli4AKE1AKEPaid : Bool
open GammaCrystalReference public

oneAK2Reference : GammaCrystalReference
oneAK2Reference = gamma-crystal-reference
  "1AK2" "10.2210/pdb1AK2/pdb" "Bos taurus" "P08166" 192
  nearGammaInLiLandscape openInPrimaryStructuralPaper
  "Li-Liu-Ji 2015, ligand-free metadynamics text/Figure 5a: two crystal structures 1AK2 and 2AK2 stay near gamma"
  "RCSB 1AK2 + Schlauderer-Schulz 1996: unligated bovine AK2, open conformation, 1.92 A"
  true false false

twoAK2Reference : GammaCrystalReference
twoAK2Reference = gamma-crystal-reference
  "2AK2" "10.2210/pdb2AK2/pdb" "Bos taurus" "P08166" 210
  nearGammaInLiLandscape openInPrimaryStructuralPaper
  "Li-Liu-Ji 2015, ligand-free metadynamics text/Figure 5a: two crystal structures 1AK2 and 2AK2 stay near gamma"
  "RCSB 2AK2 + Schlauderer-Schulz 1996: unligated bovine AK2, open conformation, 2.10 A"
  true false false

------------------------------------------------------------------------
-- WrongType / role-collapse firewalls.
------------------------------------------------------------------------

data NearGammaCreatesGammaIdentity : Set where
data OpenClassificationCreatesSameCoordinateState : Set where
data BovineReferenceCreatesEcoliSameSequence : Set where
data RoleDifferenceCreatesSourceContradiction : Set where
data PdbQidNeededForPdbIdentity : Set where

nearGammaDoesNotCreateGammaIdentity : NearGammaCreatesGammaIdentity → ⊥
nearGammaDoesNotCreateGammaIdentity ()

openClassificationDoesNotCreateSameCoordinateState : OpenClassificationCreatesSameCoordinateState → ⊥
openClassificationDoesNotCreateSameCoordinateState ()

bovineReferenceDoesNotCreateEcoliSameSequence : BovineReferenceCreatesEcoliSameSequence → ⊥
bovineReferenceDoesNotCreateEcoliSameSequence ()

roleDifferenceDoesNotCreateSourceContradiction : RoleDifferenceCreatesSourceContradiction → ⊥
roleDifferenceDoesNotCreateSourceContradiction ()

unresolvedPdbQidDoesNotBlockPdbIdentity : PdbQidNeededForPdbIdentity → ⊥
unresolvedPdbQidDoesNotBlockPdbIdentity ()

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record AdKGammaCrystalReferenceBoundary : Set where
  constructor adk-gamma-crystal-reference-boundary
  field
    liPaperMapsBothNearGamma : Bool
    primaryPaperDescribesBothOpen : Bool
    samePdbObjectsAcrossSourcesPaid : Bool
    oneAK2PdbDoiPaid : Bool
    twoAK2PdbDoiPaid : Bool
    bovineUniProtP08166Paid : Bool
    referencesAreBovine : Bool
    referencesAreEcoliSameSequence : Bool
    pdbObjectsEqualGammaState : Bool
    roleDifferenceProvesSourceContradiction : Bool
    exactPdbObjectQidsPaid : Bool
    articleQidPaid : Bool
    qidAbsenceBlocksStructuralIdentity : Bool
    sourceAuthorshipTransfersToDashiAlignment : Bool
    nextResidual : String
open AdKGammaCrystalReferenceBoundary public

canonicalAdKGammaCrystalReferenceBoundary : AdKGammaCrystalReferenceBoundary
canonicalAdKGammaCrystalReferenceBoundary = adk-gamma-crystal-reference-boundary
  true true true true true true true
  false false false false false false false
  "retain 1AK2/2AK2 as cross-source, cross-homolog structural reference points near gamma under Li-Liu-Ji's projection while preserving the primary paper's open-conformation classification. Do not use them to pay same-sequence E. coli gamma identity or named-state dLN/Delta-G/rate cells."
