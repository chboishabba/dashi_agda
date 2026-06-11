# Drosophila Genome W4 Candidate Authority Packet

Date: `2026-05-12`
Status: `candidate; checksum-bound; non-promoting`

This note records the Drosophila Release 6 genome packet as a possible W4
chemistry/calibration support surface. It does not construct W4 physical
calibration, Candidate256 authority, Brain promotion, biology recovery, or
unification.

## Authority Route

The accepted authority route candidate is:

| Field | Value |
|---|---|
| Organism | `Drosophila melanogaster` |
| Assembly accession | `GCF_000001215.4` |
| Assembly name | `Release 6 plus ISO1 MT` |
| NCBI datasets page | `https://www.ncbi.nlm.nih.gov/datasets/genome/GCF_000001215.4/` |
| NCBI FTP directory | `https://ftp.ncbi.nlm.nih.gov/genomes/all/GCF/000/001/215/GCF_000001215.4_Release_6_plus_ISO1_MT/` |
| Release 6 reference DOI | `10.1101/gr.185579.114` |
| PubMed | `25589440` |

The previously suggested DOI `10.1126/science.1237175` is rejected for this
route because it is not the Drosophila Release 6 reference-sequence paper.

## Local Artifacts

Downloaded local artifacts:

| Artifact | SHA-256 | Notes |
|---|---|---|
| `scripts/data/genome/GCF_000001215.4_Release_6_plus_ISO1_MT_genomic.fna.gz` | `e69e907b5e87ce756236dcef93e82001cfd08f1a0ed5f22e36cbbd3a87ebc57d` | 1870 FASTA records, 143726002 total bases |
| `scripts/data/genome/GCF_000001215.4_Release_6_plus_ISO1_MT_cds_from_genomic.fna.gz` | `3f379cec1d952f9a1c22e2b6dd9ff8eefce6da97ffb198cde93dc0a17c40da01` | 30802 CDS records, 61229245 bases |
| `scripts/data/genome/drosophila_release6_authority_packet.json` | generated packet | Reproducible authority and codon witness artifact |

Extractor:

```text
scripts/extract_drosophila_genome_packet.py
```

Validation:

```text
python3 -m py_compile scripts/extract_drosophila_genome_packet.py
timeout 30s agda DASHI/Physics/Closure/DrosophilaGenomeW4CandidateAuthorityReceipt.agda
```

## Codon Witness

The codon-frequency witness is computed from the CDS FASTA, not from arbitrary
frames in the raw genomic FASTA.

| Field | Value |
|---|---:|
| Total ACGT codons | `20409720` |
| Distinct ACGT codons | `64` |
| Max codon | `GAG` |
| Max codon count | `867771` |
| Min nonzero codon | `TGA` |
| Min nonzero codon count | `8978` |
| Max/min count ratio | `96.65526843394966` |
| Chi-square vs uniform 64-codon distribution | `6954583.252121048` |

This is a non-uniform codon-distribution witness. It is not a W4 calibration
law.

## Board Interpretation

This packet can honestly fill only candidate surfaces:

| W4 field class | Status |
|---|---|
| `acceptedAuthorityRoute` | Candidate route now checksum-bound and source-cited |
| `checksumBoundSelection` | Candidate selection now bound to genomic and CDS FASTA SHA-256 values |
| `nontrivialWitness` | Candidate codon non-uniformity witness computed from CDS FASTA |
| `calibrationLaw` | Missing theorem |
| `chemistryLawCompatibility` | Missing handoff proof to `BrainAtomicChemistryHandoffProfile` / W4 |
| `Candidate256PhysicalCalibrationAuthorityToken` | Still constructorless in-repo |
| `Candidate256PhysicalCalibrationExternalReceipt` | Not inhabited |

The next admissible internal work is a theorem/request surface for:

```text
Drosophila CDS codon witness
  -> TSFV-compatible chemistry-law candidate
  -> BrainAtomicChemistryHandoffProfile compatibility target
  -> Candidate256 provider request, not promotion
```

No current artifact here promotes W4.
