module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseGammaLCrystalReferenceAcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSparseCalibrationFibreExact as Sparse

------------------------------------------------------------------------
-- LIGAND-BOUND gamma_L-NEAR CRYSTAL-REFERENCE ACQUISITION
--
-- Li, Liu & Ji 2015 explicitly place PDB 1DVR and PDB 2C9Y around the gamma_L
-- state in the ligand-bound Figure-6 theta1/theta2 landscape.  The same PDB
-- objects have independent structural identities and source roles:
--
--   1DVR : mutant Saccharomyces cerevisiae adenylate kinase, ATP-analogue
--          ligated, LID-closed structural paper; DOI/PMID paid.
--   2C9Y : human mitochondrial adenylate kinase 2, B4P-bound PDB deposition;
--          RCSB lists the associated literature as "to be published".
--
-- DASHI retains the same-object cross-source identity while refusing:
--   near gamma_L -> exact gamma_L state identity,
--   cross-species structure -> E. coli same-sequence witness,
--   PDB/QID/UniProt identity -> mechanism or numeric calibration.
------------------------------------------------------------------------

liLiuJiSource : Attribution.AttributedSource
liLiuJiSource = Sparse.liLiuJi2015Source

liLiuJiReceipt : Snowball.SourceRoleSnowballReceipt liLiuJiSource
liLiuJiReceipt = Snowball.canonicalSourceRoleSnowballReceipt liLiuJiSource

oneDVRPrimaryArticle : Attribution.AttributedSource
oneDVRPrimaryArticle =
  Attribution.mkDOISource
    "Schlauderer, Proba and Schulz"
    "Structure of a mutant adenylate kinase ligated with an ATP-analogue showing domain closure over ATP"
    "Journal of Molecular Biology"
    "1996"
    "10.1006/jmbi.1996.0080"
    "https://pubmed.ncbi.nlm.nih.gov/8594191/"
    Attribution.academicArticleSource
    "pays primary 1DVR structural interpretation: mutant yeast adenylate kinase ligated with an ATP analogue, LID-closed state, 2.36 A structure; it does not pay Li-Liu-Ji gamma_L identity"
    Attribution.publicAttribution

oneDVRPrimaryReceipt : Snowball.SourceRoleSnowballReceipt oneDVRPrimaryArticle
oneDVRPrimaryReceipt = Snowball.canonicalSourceRoleSnowballReceipt oneDVRPrimaryArticle

pdb1DVRSource : Attribution.AttributedSource
pdb1DVRSource =
  Attribution.mkDOISource
    "Schlauderer, Proba and Schulz / wwPDB"
    "PDB 1DVR: mutant adenylate kinase ligated with an ATP analogue"
    "Protein Data Bank"
    "1996"
    "10.2210/pdb1DVR/pdb"
    "https://www.rcsb.org/structure/1DVR"
    Attribution.empiricalDatasetSource
    "pays stable PDB identity, Saccharomyces cerevisiae source organism, mutation status, X-ray method, 2.36 A resolution and UniProt P07170; it does not pay gamma_L state identity"
    Attribution.publicAttribution

pdb2C9YSource : Attribution.AttributedSource
pdb2C9YSource =
  Attribution.mkDOISource
    "Bunkoczi et al. / wwPDB"
    "PDB 2C9Y: structure of human adenylate kinase 2"
    "Protein Data Bank"
    "2006"
    "10.2210/pdb2C9Y/pdb"
    "https://www.rcsb.org/structure/2C9Y"
    Attribution.empiricalDatasetSource
    "pays stable PDB identity, Homo sapiens source organism, no-mutation deposition status, X-ray method, 2.10 A resolution, B4P-bound structure and UniProt P54819; associated literature is listed by RCSB as to be published"
    Attribution.publicAttribution

pdb1DVRReceipt : Snowball.SourceRoleSnowballReceipt pdb1DVRSource
pdb1DVRReceipt = Snowball.canonicalSourceRoleSnowballReceipt pdb1DVRSource

pdb2C9YReceipt : Snowball.SourceRoleSnowballReceipt pdb2C9YSource
pdb2C9YReceipt = Snowball.canonicalSourceRoleSnowballReceipt pdb2C9YSource

------------------------------------------------------------------------
-- External identity coordinates.
------------------------------------------------------------------------

oneDVRPdbIdentity : Identity.ExternalIdentityDemand
oneDVRPdbIdentity = Identity.mkOptionalIdentityDemand
  "AdK gamma_L crystal-reference acquisition"
  "PDB 1DVR deposition identity"
  "mutant yeast adenylate kinase ATP-analogue complex"
  Identity.officialIdentifier
  (Identity.verified "Protein Data Bank" "1DVR")

twoC9YPdbIdentity : Identity.ExternalIdentityDemand
twoC9YPdbIdentity = Identity.mkOptionalIdentityDemand
  "AdK gamma_L crystal-reference acquisition"
  "PDB 2C9Y deposition identity"
  "human adenylate kinase 2"
  Identity.officialIdentifier
  (Identity.verified "Protein Data Bank" "2C9Y")

oneDVRUniProt : Identity.ExternalIdentityDemand
oneDVRUniProt = Identity.mkOptionalIdentityDemand
  "AdK gamma_L crystal-reference acquisition"
  "1DVR yeast adenylate kinase UniProt identity"
  "adenylate kinase, Saccharomyces cerevisiae"
  Identity.officialIdentifier
  (Identity.verified "UniProt via RCSB" "P07170")

twoC9YUniProt : Identity.ExternalIdentityDemand
twoC9YUniProt = Identity.mkOptionalIdentityDemand
  "AdK gamma_L crystal-reference acquisition"
  "2C9Y human adenylate kinase 2 UniProt identity"
  "KAD2_HUMAN"
  Identity.officialIdentifier
  (Identity.verified "UniProt / RCSB cross-reference" "P54819")

oneDVRPrimaryPMID : Identity.ExternalIdentityDemand
oneDVRPrimaryPMID = Identity.mkOptionalIdentityDemand
  "AdK gamma_L crystal-reference acquisition"
  "1DVR primary article PubMed identity"
  "Structure of a mutant adenylate kinase ligated with an ATP-analogue showing domain closure over ATP"
  Identity.officialIdentifier
  (Identity.verified "PubMed" "8594191")

oneDVRArticleQid : Identity.ExternalIdentityDemand
oneDVRArticleQid = Identity.mkOptionalIdentityDemand
  "AdK gamma_L crystal-reference acquisition"
  "1DVR primary article Wikidata identity"
  "Schlauderer-Proba-Schulz 1996"
  Identity.wikidataQid
  (Identity.unresolved "article-level QID unresolved in inspected sources")

twoC9YArticleIdentity : Identity.ExternalIdentityDemand
twoC9YArticleIdentity = Identity.mkOptionalIdentityDemand
  "AdK gamma_L crystal-reference acquisition"
  "2C9Y associated publication identity"
  "Structure of Human Adenylate Kinase 2"
  Identity.officialIdentifier
  (Identity.unresolved "RCSB lists associated literature as 'To be published'; no DOI/PMID promoted")

oneDVRObjectQid : Identity.ExternalIdentityDemand
oneDVRObjectQid = Identity.mkOptionalIdentityDemand
  "AdK gamma_L crystal-reference acquisition"
  "PDB 1DVR object Wikidata identity"
  "1DVR"
  Identity.wikidataQid
  (Identity.unresolved "exact PDB-object QID unresolved")

twoC9YObjectQid : Identity.ExternalIdentityDemand
twoC9YObjectQid = Identity.mkOptionalIdentityDemand
  "AdK gamma_L crystal-reference acquisition"
  "PDB 2C9Y object Wikidata identity"
  "2C9Y"
  Identity.wikidataQid
  (Identity.unresolved "exact PDB-object QID unresolved")

------------------------------------------------------------------------
-- Role-sensitive same-object references.
------------------------------------------------------------------------

data SourceClassificationRole : Set where
  nearGammaLInLiLandscape : SourceClassificationRole
  lidClosedInPrimaryStructuralPaper : SourceClassificationRole
  humanAK2LigandBoundPdbStructure : SourceClassificationRole

record GammaLCrystalReference : Set where
  constructor gamma-l-crystal-reference
  field
    pdbId : String
    pdbDoi : String
    organism : String
    uniprot : String
    xrayResolutionHundredthsAngstrom : Nat
    liLandscapeRole : SourceClassificationRole
    independentStructuralRole : SourceClassificationRole
    liLocator : String
    structuralLocator : String
    samePdbObjectAcrossSourcesPaid : Bool
    exactGammaLStateIdentityPaid : Bool
    sameSequenceAsEcoli4AKE1AKEPaid : Bool
open GammaLCrystalReference public

oneDVRReference : GammaLCrystalReference
oneDVRReference = gamma-l-crystal-reference
  "1DVR" "10.2210/pdb1DVR/pdb" "Saccharomyces cerevisiae" "P07170" 236
  nearGammaLInLiLandscape lidClosedInPrimaryStructuralPaper
  "Li-Liu-Ji 2015, ligand-bound metadynamics text/Figure 6a: PDB 1DVR and 2C9Y are around gamma_L"
  "RCSB 1DVR + Schlauderer-Proba-Schulz 1996: mutant yeast AdK, ATP-analogue ligated, LID-closed, 2.36 A"
  true false false

twoC9YReference : GammaLCrystalReference
twoC9YReference = gamma-l-crystal-reference
  "2C9Y" "10.2210/pdb2C9Y/pdb" "Homo sapiens" "P54819" 210
  nearGammaLInLiLandscape humanAK2LigandBoundPdbStructure
  "Li-Liu-Ji 2015, ligand-bound metadynamics text/Figure 6a: PDB 1DVR and 2C9Y are around gamma_L"
  "RCSB 2C9Y: human mitochondrial AK2, B4P-bound, no mutation, 2.10 A; associated literature to be published"
  true false false

------------------------------------------------------------------------
-- WrongType / source-role firewalls.
------------------------------------------------------------------------

data NearGammaLCreatesGammaLIdentity : Set where
data CrossSpeciesReferenceCreatesEcoliSameSequence : Set where
data PdbIdentityCreatesLigandBoundMechanism : Set where
data UnresolvedPublicationMayBeInvented : Set where
data QidCreatesGammaLScientificAuthority : Set where

nearGammaLDoesNotCreateGammaLIdentity : NearGammaLCreatesGammaLIdentity → ⊥
nearGammaLDoesNotCreateGammaLIdentity ()

crossSpeciesReferenceDoesNotCreateEcoliSameSequence : CrossSpeciesReferenceCreatesEcoliSameSequence → ⊥
crossSpeciesReferenceDoesNotCreateEcoliSameSequence ()

pdbIdentityDoesNotCreateLigandBoundMechanism : PdbIdentityCreatesLigandBoundMechanism → ⊥
pdbIdentityDoesNotCreateLigandBoundMechanism ()

unresolvedPublicationCannotBeInvented : UnresolvedPublicationMayBeInvented → ⊥
unresolvedPublicationCannotBeInvented ()

qidDoesNotCreateGammaLScientificAuthority : QidCreatesGammaLScientificAuthority → ⊥
qidDoesNotCreateGammaLScientificAuthority ()

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record AdKGammaLCrystalReferenceBoundary : Set where
  constructor adk-gamma-l-crystal-reference-boundary
  field
    liPaperMapsBothNearGammaL : Bool
    samePdbObjectsAcrossSourcesPaid : Bool
    oneDVRPdbDoiPaid : Bool
    twoC9YPdbDoiPaid : Bool
    oneDVRPrimaryArticleIdentityPaid : Bool
    oneDVRUniProtP07170Paid : Bool
    twoC9YUniProtP54819Paid : Bool
    twoC9YPrimaryPublicationResolved : Bool
    referencesAreCrossSpecies : Bool
    referencesAreEcoliSameSequence : Bool
    pdbObjectsEqualGammaLState : Bool
    pdbIdentityCreatesLigandBoundMechanism : Bool
    exactPdbObjectQidsPaid : Bool
    qidCreatesGammaLScientificAuthority : Bool
    sourceAuthorshipTransfersToDashiAlignment : Bool
    nextResidual : String
open AdKGammaLCrystalReferenceBoundary public

canonicalAdKGammaLCrystalReferenceBoundary : AdKGammaLCrystalReferenceBoundary
canonicalAdKGammaLCrystalReferenceBoundary = adk-gamma-l-crystal-reference-boundary
  true true true true true true true
  false true false false false false false false
  "retain 1DVR/2C9Y as cross-source, cross-species structural reference points around gamma_L under Li-Liu-Ji's ligand-bound projection. Do not promote either PDB object to exact gamma_L identity, E. coli same-sequence evidence, missing theta/dLN state coordinates, or ligand-bound mechanism authority; leave the 2C9Y publication identity unresolved because RCSB lists it only as to be published."
