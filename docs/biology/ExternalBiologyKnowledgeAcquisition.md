# External biological knowledge acquisition and admission

This note owns the acquisition boundary for UniProt-like biological databases.
It complements `KitzerowBH4PriorityAcquisition.md`; it does not replace the
scientific-support / priority / contact / attribution product formalized there.

## Architecture

External database/API -> immutable response bytes -> SHA-256/release receipt ->
normalized finite certificate -> Agda database assertion -> cross-database
mapping witness -> consumer-specific admission.

The formal owners are:

- `DASHI.Biology.ExternalBiologyEvidenceCore`
- `DASHI.Biology.ExternalBiologyMappingRevisionExact`
- `DASHI.Biology.ExternalBiologyConsumerAdmissionExact`
- `DASHI.Biology.UniProtExternalKnowledgeExact`
- `DASHI.Biology.KitzerowUniProtCrossPollinationExact`
- `DASHI.Biology.ExternalBiologyRegression`

## Identity firewall

The following are intentionally distinct unless a witness pays the relation:

gene != transcript != UniProt entry != canonical sequence != isoform !=
processed chain != PDB chain != predicted structure != physical molecule.

A cross-reference records a relation; it is not definitionally an equality.
Residue-level PDB/UniProt consumption should use a SIFTS/PDBe mapping witness.
AlphaFoldDB is a predicted-structure source and is not promoted to an
experimentally determined structure.

## Evidence firewall

Reviewed/unreviewed status, evidence kind, publication support, prediction and
consumer applicability are separate coordinates. A reviewed UniProt record is
not automatically direct experimental proof. A curated database assertion may
be admissible for a reaction-annotation consumer while remaining insufficient
for a disease-mechanism or clinical-action consumer.

## Revision firewall

Entry revision, sequence revision and annotation revision are distinct. Absence
from a current dataset does not imply biological nonexistence; historical
records remain audit evidence. Newer releases do not automatically erase older
claims or their provenance.

## Concrete BH4 witness

The initial witness is human QDPR / UniProtKB `P09417` (`DHPR_HUMAN`). The
current UniProt entry records a reviewed 244-aa canonical isoform `P09417-1`,
sequence version 2 with MD5 `01EAB47E5C55913647DB7DBAD571D960`, catalytic
activity linked to `RHEA:17869`, PDB structure `9DTW`, and an AlphaFoldDB
cross-reference.

`KitzerowUniProtCrossPollinationExact` maps the bounded QDPR/BH4-regeneration
database assertion to the existing `bh4Availability` target. This can pay a
real biochemical node in the atlas. It cannot confirm the complete Kitzerow
cascade and cannot establish Kitzerow priority, access/contact, derivation or
an attribution breach.

## Acquisition command

```bash
python3 scripts/acquire_uniprot_bio_certificate.py P09417 \
  --output artifacts/biology/uniprot-P09417-certificate.json
```

The certificate records the exact raw-response SHA-256, UniProt release headers
when supplied, entry audit/version information, organism, sequence checksums,
selected cross-references and explicit non-promotion flags.

The checked-in Agda snapshot intentionally remains `exactBinaryPinned = false`
until such a certificate is acquired in the execution environment. This keeps
network acquisition as an explicit residual rather than fabricating a digest.

## Next adapters

The same substrate is designed for UniParc (sequence-history identity),
InterPro (domain/family assertions), GO (ontology annotations), Rhea/ChEBI
(reaction/chemical identity), PDB + PDBe/SIFTS (experimental structure and
residue mappings), AlphaFoldDB (predicted structure/confidence), Ensembl/NCBI
(gene/transcript provenance), and later Reactome/IntAct/STRING/BRENDA where a
consumer requires them.

Every adapter must preserve source attribution, release/version provenance,
relation type, evidence kind, and the same non-promotion boundaries.
