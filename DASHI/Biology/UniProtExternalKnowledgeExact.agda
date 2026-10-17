module DASHI.Biology.UniProtExternalKnowledgeExact where

open import DASHI.Core.Prelude

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.GenericReceipt as Receipt
import DASHI.Biology.ExternalBiologyEvidenceCore as External
import DASHI.Biology.ExternalBiologyMappingRevisionExact as Mapping
import DASHI.Biology.ExternalBiologyConsumerAdmissionExact as Admission

------------------------------------------------------------------------
-- UNIPROT / QDPR CONCRETE WITNESS
--
-- The P09417 REST response was acquired against UniProt release 2026_03 and
-- byte-pinned by scripts/acquire_uniprot_bio_certificate.py.  The immutable
-- response digest is retained below; exact acquisition still does not promote
-- database curation into biological truth or downstream mechanism.
------------------------------------------------------------------------

uniProtServiceSource : Source.AttributedSource
uniProtServiceSource =
  Source.mkNoDOISource
    "UniProt Consortium"
    "UniProtKB REST/API and entry service"
    "UniProt"
    "2026"
    "https://rest.uniprot.org/"
    Source.institutionalSource
    "versioned protein sequence, annotation, evidence and cross-reference source"
    Source.publicAttribution

uniProt2026_03 : External.DatasetSnapshot
uniProt2026_03 =
  External.datasetSnapshot
    External.uniProtKB
    "2026_03"
    "2026-10-17"
    "sha256:7ef73e73b15eb967db526cc5ba2970965992ff348e758b57057e1bc61def3936"
    "UniProt REST OpenAPI / UniProtKB JSON; X-UniProt-Release 2026_03; release date 02-September-2026"
    uniProtServiceSource
    true

qdprProtein : External.ProteinRef
qdprProtein =
  External.proteinRef
    "P09417"
    "DHPR_HUMAN"
    2
    "P09417-1"
    9606
    External.reviewed

qdprSequence : External.SequenceWitness
qdprSequence =
  External.sequenceWitness
    qdprProtein
    244
    "MD5"
    "01EAB47E5C55913647DB7DBAD571D960"
    true
    "UniProtKB P09417 canonical isoform P09417-1; sequence version 2; CRC64 0852F9F0CA38AB1C"

qdprCatalysisEvidence : External.EvidenceBundle
qdprCatalysisEvidence =
  External.evidenceBundle
    External.curatedLiterature
    "UniProtKB curated catalytic-activity annotation"
    "entry-linked publications retained by UniProt; primary-paper admission remains separate"
    "P09417 catalytic activity lists supporting publications"
    "UniProtKB"
    false
    false

qdprBH4RegenerationClaim : External.BiologicalClaim
qdprBH4RegenerationClaim =
  External.mkDatabaseClaim
    "UNIPROT-P09417-RHEA17869"
    qdprProtein
    External.catalyzes
    "RHEA:17869; quinonoid-dihydrobiopterin/tetrahydrobiopterin redox reaction as curated on P09417"
    qdprCatalysisEvidence
    uniProt2026_03
    "UniProtKB curates QDPR/P09417 as dihydropteridine reductase and links catalytic activity to Rhea; this pays a bounded BH4-regeneration annotation node."
    "The UniProt record does not establish an autism mechanism, whole-cascade causality, clinical efficacy, temporal priority, source access or attribution breach."

qdprToRhea17869 : Mapping.CrossDatabaseMapping
qdprToRhea17869 =
  Mapping.mkMapping
    "MAP-P09417-RHEA17869"
    External.uniProtKB
    "P09417"
    External.rhea
    "RHEA:17869"
    Mapping.reactionMapping
    "UniProtKB P09417 catalytic-activity cross-reference"
    false

qdprToPDB9DTW : Mapping.CrossDatabaseMapping
qdprToPDB9DTW =
  Mapping.mkMapping
    "MAP-P09417-PDB9DTW"
    External.uniProtKB
    "P09417 canonical positions 1-244"
    External.pdb
    "9DTW chain A positions 1-244"
    Mapping.experimentalStructureMapping
    "UniProtKB structure cross-reference; residue-level exactness should be paid by SIFTS/PDBe when consumed"
    false

qdprToAlphaFold : Mapping.CrossDatabaseMapping
qdprToAlphaFold =
  Mapping.mkMapping
    "MAP-P09417-AFDB"
    External.uniProtKB
    "P09417"
    External.alphaFoldDB
    "P09417"
    Mapping.structurePredictionMapping
    "UniProtKB AlphaFoldDB cross-reference"
    false

qdprReactionAnnotationAssessment : Admission.ConsumerAssessment
qdprReactionAnnotationAssessment =
  Admission.mkAssessment
    "ASSESS-P09417-RHEA"
    qdprBH4RegenerationClaim
    Admission.reactionAnnotationConsumer
    Admission.curatedLiteratureGrade
    Admission.admissible
    "Sufficient to consume the curated UniProt-to-Rhea annotation as a database claim with provenance."
    "Primary experimental paper is still required to promote a specific biochemical experiment beyond the curated database assertion."

qdprMechanismAssessment : Admission.ConsumerAssessment
qdprMechanismAssessment =
  Admission.mkAssessment
    "ASSESS-P09417-MECHANISM"
    qdprBH4RegenerationClaim
    Admission.mechanisticModelConsumer
    Admission.curatedLiteratureGrade
    Admission.insufficient
    "The annotation can seed a mechanistic hypothesis but does not by itself pay a disease-level causal mechanism."
    "Acquire and admit primary biochemical/disease experiments and same-object pathway adapters."

qdprClinicalAssessment : Admission.ConsumerAssessment
qdprClinicalAssessment =
  Admission.mkAssessment
    "ASSESS-P09417-CLINICAL"
    qdprBH4RegenerationClaim
    Admission.clinicalActionConsumer
    Admission.curatedLiteratureGrade
    Admission.insufficient
    "A curated protein annotation is not a clinical-action authorization."
    "Clinical evidence, population applicability, intervention evidence and safety/benefit owners remain required."

canonicalUniProtExternalKnowledgeReceipt : Receipt.GenericReceipt
canonicalUniProtExternalKnowledgeReceipt =
  Receipt.mkNonPromotingReceipt
    "UniProt external knowledge witness"
    "DASHI.Biology.UniProtExternalKnowledgeExact"
    "P09417/QDPR byte-pinned sequence, BH4-regeneration claim and Rhea/PDB/AlphaFold mappings"
    "instantiates the reusable external-biology substrate on one reviewed human BH4-pathway protein with an exact 2026_03 REST-response SHA-256 receipt"
    "exact acquisition does not prove a whole disease model or clinical action; cross-references do not collapse entity identity"
    "python3 scripts/acquire_uniprot_bio_certificate.py P09417 && agda -i . DASHI/Biology/UniProtExternalKnowledgeExact.agda"
