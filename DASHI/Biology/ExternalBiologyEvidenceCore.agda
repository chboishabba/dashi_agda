module DASHI.Biology.ExternalBiologyEvidenceCore where

open import DASHI.Core.Prelude

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.EmpiricalSourceDiligenceAdmissionExact as Diligence
import DASHI.Core.GenericReceipt as Receipt

------------------------------------------------------------------------
-- EXTERNAL BIOLOGY EVIDENCE CORE
--
-- Domain refinement of the repo-wide attributed-source and empirical-source
-- diligence owners.  A database record is represented as a versioned source
-- assertion with biological identity/evidence coordinates; it is never
-- definitionally promoted to biological truth or applicability.
------------------------------------------------------------------------

data BioSource : Set where
  uniProtKB : BioSource
  uniParc : BioSource
  interPro : BioSource
  geneOntology : BioSource
  rhea : BioSource
  pdb : BioSource
  pdbeSIFTS : BioSource
  alphaFoldDB : BioSource
  ensembl : BioSource
  ncbi : BioSource
  reactome : BioSource
  chebi : BioSource
  namedBioSource : String → BioSource

data ReviewStatus : Set where
  reviewed : ReviewStatus
  unreviewed : ReviewStatus
  reviewStatusNotApplicable : ReviewStatus
  reviewStatusUnknown : ReviewStatus

record DatasetSnapshot : Set where
  constructor datasetSnapshot
  field
    source : BioSource
    release : String
    acquiredAt : String
    contentDigestReference : String
    schemaReference : String
    sourceRecord : Source.AttributedSource
    exactBinaryPinned : Bool

open DatasetSnapshot public

data BioEntityKind : Set where
  gene : BioEntityKind
  transcript : BioEntityKind
  proteinEntry : BioEntityKind
  canonicalProteinSequence : BioEntityKind
  proteinIsoform : BioEntityKind
  processedChain : BioEntityKind
  structureModel : BioEntityKind
  experimentallyDeterminedStructure : BioEntityKind
  reaction : BioEntityKind
  ontologyTerm : BioEntityKind
  domainOrFamily : BioEntityKind
  smallMolecule : BioEntityKind

record ProteinRef : Set where
  constructor proteinRef
  field
    accession : String
    entryName : String
    sequenceVersion : Nat
    isoform : String
    taxon : Nat
    reviewStatus : ReviewStatus

open ProteinRef public

record SequenceWitness : Set where
  constructor sequenceWitness
  field
    owner : ProteinRef
    length : Nat
    checksumAlgorithm : String
    checksum : String
    canonicalSequence : Bool
    sequenceSourceReference : String

open SequenceWitness public

data ProteinIdentityRelation : Set where
  sameDatabaseEntry : ProteinIdentityRelation
  sameCanonicalSequence : ProteinIdentityRelation
  sameIsoform : ProteinIdentityRelation
  sameGeneProduct : ProteinIdentityRelation
  sequenceEquivalent : ProteinIdentityRelation
  relatedButNotIdentical : ProteinIdentityRelation

record IdentityWitness : Set where
  constructor identityWitness
  field
    leftReference : String
    rightReference : String
    relation : ProteinIdentityRelation
    evidenceReference : String
    exactSequenceEqualityWitnessed : Bool
    databaseIdentifierEqualityWitnessed : Bool

open IdentityWitness public

data EvidenceKind : Set where
  directExperiment : EvidenceKind
  curatedLiterature : EvidenceKind
  curatorInference : EvidenceKind
  sequenceSimilarity : EvidenceKind
  phylogeneticInference : EvidenceKind
  ruleBasedAnnotation : EvidenceKind
  computationalPrediction : EvidenceKind
  languageModelPrediction : EvidenceKind
  importedAnnotation : EvidenceKind
  evidenceKindUnknown : EvidenceKind

record EvidenceBundle : Set where
  constructor evidenceBundle
  field
    kind : EvidenceKind
    methodReference : String
    evidenceCodeReference : String
    citationReference : String
    sourceDatabaseReference : String
    directExperimentalSupport : Bool
    predictionOnly : Bool

open EvidenceBundle public

data BioPredicate : Set where
  hasFunction : BioPredicate
  catalyzes : BioPredicate
  hasFeature : BioPredicate
  binds : BioPredicate
  locatedAt : BioPredicate
  participatesIn : BioPredicate
  hasDomain : BioPredicate
  hasStructure : BioPredicate
  predictsStructureOf : BioPredicate
  encodedBy : BioPredicate
  mapsResidueTo : BioPredicate
  hasTaxon : BioPredicate
  hasSequence : BioPredicate
  namedBioPredicate : String → BioPredicate

record BiologicalClaim : Set where
  constructor biologicalClaim
  field
    claimId : String
    subject : ProteinRef
    predicate : BioPredicate
    objectReference : String
    evidence : EvidenceBundle
    snapshot : DatasetSnapshot
    boundedReading : String
    interpretationBoundary : String
    datasetAssertsClaim : Bool
    datasetAssertionCreatesBiologicalTruth : Bool
    datasetAssertionCreatesBiologicalTruthIsFalse :
      datasetAssertionCreatesBiologicalTruth ≡ false

open BiologicalClaim public

mkDatabaseClaim :
  String → ProteinRef → BioPredicate → String → EvidenceBundle →
  DatasetSnapshot → String → String → BiologicalClaim
mkDatabaseClaim claimId subject predicate object evidence snapshot reading boundary =
  biologicalClaim
    claimId subject predicate object evidence snapshot reading boundary
    true false refl

record ClaimBoundary : Set where
  constructor claimBoundary
  field
    datasetAssertionCreatesBiologicalTruth : Bool
    datasetAssertionCreatesBiologicalTruthIsFalse :
      datasetAssertionCreatesBiologicalTruth ≡ false
    reviewedStatusImpliesDirectExperimentalProof : Bool
    reviewedStatusImpliesDirectExperimentalProofIsFalse :
      reviewedStatusImpliesDirectExperimentalProof ≡ false
    computationalPredictionIsExperiment : Bool
    computationalPredictionIsExperimentIsFalse :
      computationalPredictionIsExperiment ≡ false
    crossReferenceCreatesSameObjectIdentity : Bool
    crossReferenceCreatesSameObjectIdentityIsFalse :
      crossReferenceCreatesSameObjectIdentity ≡ false
    canonicalProteinEqualsEveryTranscriptTranslation : Bool
    canonicalProteinEqualsEveryTranscriptTranslationIsFalse :
      canonicalProteinEqualsEveryTranscriptTranslation ≡ false

canonicalClaimBoundary : ClaimBoundary
canonicalClaimBoundary =
  claimBoundary false refl false refl false refl false refl false refl

------------------------------------------------------------------------
-- Connection back to repo-wide source diligence.
------------------------------------------------------------------------

record BiologicalSourceAdmission : Set where
  constructor biologicalSourceAdmission
  field
    claim : BiologicalClaim
    diligence : Diligence.EmpiricalFactAdmission
    biologicalIdentityReference : String
    evidenceInterpretationReference : String
    admissionCreatesTruth : Bool
    admissionCreatesTruthIsFalse : admissionCreatesTruth ≡ false

open BiologicalSourceAdmission public

canonicalExternalBiologyReceipt : Receipt.GenericReceipt
canonicalExternalBiologyReceipt =
  Receipt.mkNonPromotingReceipt
    "external biology evidence core"
    "DASHI.Biology.ExternalBiologyEvidenceCore"
    "DatasetSnapshot / ProteinRef / SequenceWitness / BiologicalClaim / EvidenceBundle"
    "refines attributed-source and empirical-source diligence into versioned biological database assertions with explicit identity and evidence coordinates"
    "database assertion, review status, prediction, cross-reference and canonical-sequence selection do not create biological truth, same-object identity, or downstream applicability"
    "agda -i . DASHI/Biology/ExternalBiologyEvidenceCore.agda"
