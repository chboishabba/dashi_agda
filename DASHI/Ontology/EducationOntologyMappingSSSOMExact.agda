module DASHI.Ontology.EducationOntologyMappingSSSOMExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Analysis.SourceBackedTheoremTransportBidiExact as Transport
import DASHI.Cognition.PNF.WikidataRepairProposal as Repair
import DASHI.Ontology.InferenceLanguageIndexedAlignmentSafetyExact as Alignment

------------------------------------------------------------------------
-- SOURCE / PRIOR-ART BOUNDARY
--
-- SSSOM:
--   Simple Standard for Sharing Ontological Mappings, Mapping Commons.
--   The standard models a mapping as a subject/predicate/object correspondence
--   plus metadata, including a required mapping justification and optional
--   provenance/reviewer/confidence/source-version fields.  Mapping-set metadata
--   includes an identifier, versioning information and a licence.
--
-- lgbtDB:
--   user-supplied project locator:
--     https://lgbtdb.wikibase.cloud/wiki/Project:Mappings
--   Live lgbtDB item pages observed during this tranche expose mapping subject
--   source, mapping subject, mapping object source, mapping object and mapping
--   predicate as explicit statement/reference fields.  The exact project page
--   was not available through the retrieval cache, so this module does not
--   attribute additional unobserved policy claims to that page.
--
-- Rosario / IBM prior art, as already recorded by SensibLaw:
--   "Reasoning about concepts with LLMs: Inconsistencies abound".
--   SensibLaw attributes to it bounded concept-hierarchy consistency benchmark
--   and scorer framing.  DASHI/SensibLaw explicitly do not claim reproduction
--   or identity with Rosario's method.
------------------------------------------------------------------------

data MappingSourceClaim : Set where
  sssomCoreTripleAndJustification : MappingSourceClaim
  sssomMappingSetMetadata : MappingSourceClaim
  lgbtDBExplicitMappingFieldsObserved : MappingSourceClaim
  rosarioBoundedHierarchyBenchmarkFraming : MappingSourceClaim

sssomSource : Transport.SourceBackedClaim
sssomSource = record
  { Transport.SourceClaim = MappingSourceClaim
  ; Transport.sourceReceipt = sssomCoreTripleAndJustification
  ; Transport.sourceName = "Mapping Commons, Simple Standard for Sharing Ontological Mappings (SSSOM)"
  ; Transport.sourceLocator = "https://mapping-commons.github.io/sssom/"
  ; Transport.reading = "source standard for exchange/provenance of mappings; semantic promotion into local ontology truth requires an explicit local weld"
  }

lgbtDBSource : Transport.SourceBackedClaim
lgbtDBSource = record
  { Transport.SourceClaim = MappingSourceClaim
  ; Transport.sourceReceipt = lgbtDBExplicitMappingFieldsObserved
  ; Transport.sourceName = "lgbtDB mapping surface"
  ; Transport.sourceLocator = "https://lgbtdb.wikibase.cloud/wiki/Project:Mappings"
  ; Transport.reading = "bounded attribution: explicit mapping fields are observed on live item pages; no stronger project-policy claim is imported here"
  }

rosarioSource : Transport.SourceBackedClaim
rosarioSource = record
  { Transport.SourceClaim = MappingSourceClaim
  ; Transport.sourceReceipt = rosarioBoundedHierarchyBenchmarkFraming
  ; Transport.sourceName = "Rosario et al., Reasoning about concepts with LLMs: Inconsistencies abound"
  ; Transport.sourceLocator = "SensibLaw docs/planning/wikimedia_prior_work_and_originality_note_20260326.md; source 2405.20163v1_rosario.pdf"
  ; Transport.reading = "prior-art benchmark/scorer framing only; adjacency or partial parity is not method identity or reproduction"
  }

------------------------------------------------------------------------
-- SSSOM-SHAPED LOCAL MAPPING CARRIER
--
-- Predicate identity is first-class.  A mapping row is not a generic
-- 'equivalence edge'.  In particular, SKOS exact/broad/narrow/related and OWL
-- equivalent-class semantics remain distinct constructors here.
------------------------------------------------------------------------

data MappingPredicate : Set where
  skosExactMatch : MappingPredicate
  skosBroadMatch : MappingPredicate
  skosNarrowMatch : MappingPredicate
  skosRelatedMatch : MappingPredicate
  owlEquivalentClass : MappingPredicate
  rdfsSubClassOf : MappingPredicate
  localCorrespondence : MappingPredicate

data MappingJustificationKind : Set where
  lexicalMatching : MappingJustificationKind
  logicalReasoning : MappingJustificationKind
  manualMappingCuration : MappingJustificationKind
  importedSourceAssertion : MappingJustificationKind
  otherJustification : MappingJustificationKind

record SSSOMMapping : Set where
  constructor sssomMapping
  field
    subjectId : String
    mappingPredicate : MappingPredicate
    objectId : String
    mappingJustification : MappingJustificationKind
    authorId : String
    reviewerId : String
    confidence : Nat
    subjectSource : String
    subjectSourceVersion : String
    objectSource : String
    objectSourceVersion : String
    mappingDate : String
    mappingComment : String

open SSSOMMapping public

record SSSOMMappingSet : Set where
  constructor sssomMappingSet
  field
    mappingSetId : String
    mappingSetVersion : String
    mappingSetLicense : String
    mappings : List SSSOMMapping

open SSSOMMappingSet public

------------------------------------------------------------------------
-- PREDICATE NON-COLLAPSE
------------------------------------------------------------------------

exactMatchNotEquivalentClass : skosExactMatch ≡ owlEquivalentClass → ⊥
exactMatchNotEquivalentClass ()

broadMatchNotExactMatch : skosBroadMatch ≡ skosExactMatch → ⊥
broadMatchNotExactMatch ()

narrowMatchNotExactMatch : skosNarrowMatch ≡ skosExactMatch → ⊥
narrowMatchNotExactMatch ()

relatedMatchNotExactMatch : skosRelatedMatch ≡ skosExactMatch → ⊥
relatedMatchNotExactMatch ()

subclassNotEquivalentClass : rdfsSubClassOf ≡ owlEquivalentClass → ⊥
subclassNotEquivalentClass ()

------------------------------------------------------------------------
-- MAPPING REVIEW / TRUTH / INFERENCE AUTHORITY
--
-- SSSOM records mappings and their evidence/provenance.  A row, even reviewed,
-- does not by itself grant arbitrary ontology-truth or inference-language
-- authority.  Admission and downstream inference remain consumer-relative.
------------------------------------------------------------------------

data MappingReviewState : Set where
  mappingForReviewOnly : MappingReviewState
  reviewedMapping : MappingReviewState

data MappingTruthPermission : MappingReviewState → Set where

data MappingInferencePromotionPermission : MappingReviewState → Set where

mappingCannotAssertOntologyTruth :
  MappingTruthPermission mappingForReviewOnly → ⊥
mappingCannotAssertOntologyTruth ()

reviewedMappingCannotPromoteAllInferenceLanguages :
  MappingInferencePromotionPermission reviewedMapping → ⊥
reviewedMappingCannotPromoteAllInferenceLanguages ()

existingRepairReviewAuthority : Repair.RepairProposalAuthority
existingRepairReviewAuthority = Repair.proposalForReviewOnly

------------------------------------------------------------------------
-- CONSUMER / INFERENCE-LANGUAGE SAFETY REUSE
--
-- The existing owner already proves that a subclass-preserving alignment can be
-- safe for subclass lookup while remaining unsafe for disjointness reasoning.
-- We expose those exact Boolean observations here rather than inventing a
-- second alignment-safety model.
------------------------------------------------------------------------

subclassOnlySafeForSubclass : Bool
subclassOnlySafeForSubclass =
  Alignment.safeFor Alignment.subclassOnlyAlignment Alignment.subclassLanguage

subclassOnlySafeForDisjointness : Bool
subclassOnlySafeForDisjointness =
  Alignment.safeFor Alignment.subclassOnlyAlignment Alignment.disjointnessLanguage

subclassOnlySafeForSubclassIsTrue : subclassOnlySafeForSubclass ≡ true
subclassOnlySafeForSubclassIsTrue = Alignment.subclassOnlyIsSafeForSubclassLookup

subclassOnlySafeForDisjointnessIsFalse : subclassOnlySafeForDisjointness ≡ false
subclassOnlySafeForDisjointnessIsFalse = Alignment.subclassOnlyIsNotSafeForDisjointness

------------------------------------------------------------------------
-- EDUCATION / REPAIR WORKFLOW FOR MAPPINGS
--
-- A learner/curator may propose a mapping from lexical or structural evidence,
-- but review records the mapping rather than manufacturing equivalence.
-- Conflicts are review findings that may route into the existing ontology
-- repair lane; they are not automatic mutation commands.
------------------------------------------------------------------------

data MappingReviewFinding : Set where
  noObservedMappingConflict : MappingReviewFinding
  predicateTooStrong : MappingReviewFinding
  sourceVersionDrift : MappingReviewFinding
  hierarchyConflict : MappingReviewFinding
  disjointnessConflict : MappingReviewFinding
  unresolvedMappingConflict : MappingReviewFinding

record MappingReviewEnvelope : Set where
  constructor mappingReviewEnvelope
  field
    candidateMapping : SSSOMMapping
    reviewState : MappingReviewState
    finding : MappingReviewFinding
    reviewProvenance : List String

open MappingReviewEnvelope public

data MappingRepairAuthority : Set where
  mappingRepairSuggestionOnly : MappingRepairAuthority

data MappingRepairMutationPermission : MappingRepairAuthority → Set where

mappingRepairCannotMutateOntology :
  MappingRepairMutationPermission mappingRepairSuggestionOnly → ⊥
mappingRepairCannotMutateOntology ()

------------------------------------------------------------------------
-- CONFIDENCE / JUSTIFICATION ARE METADATA, NOT PREDICATE REWRITES
------------------------------------------------------------------------

sampleManualExactMapping : SSSOMMapping
sampleManualExactMapping =
  sssomMapping
    "LGBTDB:example-subject"
    skosExactMatch
    "WIKIDATA:example-object"
    manualMappingCuration
    "curator"
    "reviewer"
    95
    "lgbtDB"
    "observed-version"
    "Wikidata"
    "observed-version"
    "2026-10-12"
    "example fixture only; not a claim about a live identifier pair"

sampleMappingSet : SSSOMMappingSet
sampleMappingSet =
  sssomMappingSet
    "https://example.invalid/dashi/education-ontology-mappings"
    "0"
    "CC-BY-4.0"
    (sampleManualExactMapping ∷ [])

confidenceLeavesPredicate :
  mappingPredicate sampleManualExactMapping ≡ skosExactMatch
confidenceLeavesPredicate = refl

justificationLeavesPredicate :
  mappingPredicate sampleManualExactMapping ≡ skosExactMatch
justificationLeavesPredicate = refl

------------------------------------------------------------------------
-- ROSARIO ATTRIBUTION / ORIGINALITY FIREWALL
------------------------------------------------------------------------

data RosarioMethodIdentityPermission : Set where

rosarioPriorArtDoesNotEstablishMethodIdentity :
  RosarioMethodIdentityPermission → ⊥
rosarioPriorArtDoesNotEstablishMethodIdentity ()

------------------------------------------------------------------------
-- STATUS RECEIPT
------------------------------------------------------------------------

record MappingGovernanceStatus : Set where
  constructor mappingGovernanceStatus
  field
    sssomCoreRepresented : Bool
    predicateKindsRemainDistinct : Bool
    mappingProvenanceRepresented : Bool
    mappingTruthRequiresSeparateAdmission : Bool
    inferenceSafetyIsConsumerRelative : Bool
    mappingRepairRequiresReview : Bool
    rosarioIsPriorArtNotRepoIdentity : Bool
    lgbtDBMappingFieldsBoundedlyAttributed : Bool

    sssomCoreRepresentedIsTrue : sssomCoreRepresented ≡ true
    predicateKindsRemainDistinctIsTrue : predicateKindsRemainDistinct ≡ true
    mappingProvenanceRepresentedIsTrue : mappingProvenanceRepresented ≡ true
    mappingTruthRequiresSeparateAdmissionIsTrue : mappingTruthRequiresSeparateAdmission ≡ true
    inferenceSafetyIsConsumerRelativeIsTrue : inferenceSafetyIsConsumerRelative ≡ true
    mappingRepairRequiresReviewIsTrue : mappingRepairRequiresReview ≡ true
    rosarioIsPriorArtNotRepoIdentityIsTrue : rosarioIsPriorArtNotRepoIdentity ≡ true
    lgbtDBMappingFieldsBoundedlyAttributedIsTrue : lgbtDBMappingFieldsBoundedlyAttributed ≡ true

open MappingGovernanceStatus public

canonicalMappingGovernanceStatus : MappingGovernanceStatus
canonicalMappingGovernanceStatus =
  mappingGovernanceStatus
    true true true true true true true true
    refl refl refl refl refl refl refl refl
