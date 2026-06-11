# Drosophila Codon Witness To Candidate256 Map

Date: `2026-05-12`
Status: `non-promoting witness map; no calibration`

This note audits the local Drosophila Release 6 packet and records the minimal
map from the observed 64-codon CDS witness into the existing Candidate256
carrier surface. It is a checksum-bound, nontrivial witness map only. It does
not construct W4 physical calibration, a chemistry law, a Candidate256
authority token, a physical unit carrier, or a promotion receipt.

## Local Packet Audit

Packet:

```text
scripts/data/genome/drosophila_release6_authority_packet.json
```

Source FASTA artifacts recorded by the packet:

| Artifact | Recorded path | Recorded SHA-256 | Local audit |
|---|---|---|---|
| Genomic FASTA | `scripts/data/genome/GCF_000001215.4_Release_6_plus_ISO1_MT_genomic.fna.gz` | `e69e907b5e87ce756236dcef93e82001cfd08f1a0ed5f22e36cbbd3a87ebc57d` | path exists; checksum matches |
| CDS FASTA | `scripts/data/genome/GCF_000001215.4_Release_6_plus_ISO1_MT_cds_from_genomic.fna.gz` | `3f379cec1d952f9a1c22e2b6dd9ff8eefce6da97ffb198cde93dc0a17c40da01` | path exists; checksum matches |

Authority metadata audit:

| Field | Value |
|---|---|
| Assembly accession | `GCF_000001215.4` |
| Assembly name | `Release 6 plus ISO1 MT` |
| Organism | `Drosophila melanogaster` |
| Release 6 reference DOI | `10.1101/gr.185579.114` |
| Release 6 PubMed | `25589440` |
| Rejected prior DOI | `10.1126/science.1237175` |
| Authority metadata SHA-256 | `8e68338ea742454d7854721773f7d302b060ad53ffb79fae7b3f70996f02b902` |

The packet is reproducible from:

```text
python3 scripts/extract_drosophila_genome_packet.py \
  --genomic scripts/data/genome/GCF_000001215.4_Release_6_plus_ISO1_MT_genomic.fna.gz \
  --cds scripts/data/genome/GCF_000001215.4_Release_6_plus_ISO1_MT_cds_from_genomic.fna.gz \
  --output /tmp/drosophila_release6_authority_packet.recomputed.json
```

The recomputed JSON has SHA-256:

```text
1ccfc2df5af820fcc6efe9eb46d809d9e8d393283e59dfbc3abdcced59db95eb
```

which matches the local packet byte-for-byte.

## Codon Nonuniformity Witness

The codon witness is computed from the CDS FASTA in frame, with ambiguous
codons skipped. It is not computed from arbitrary genomic FASTA frames.

| Field | Value |
|---|---:|
| CDS sequence count | `30802` |
| Total ACGT codons | `20409720` |
| Distinct ACGT codons | `64` |
| Skipped ambiguous codons | `0` |
| Skipped partial bases | `85` |
| Max codon | `GAG` |
| Max codon count | `867771` |
| Min nonzero codon | `TGA` |
| Min nonzero codon count | `8978` |
| Max/min count ratio | `96.65526843394966` |
| Chi-square vs uniform 64-codon distribution | `6954583.252121048` |

This is a nonuniformity witness because all 64 ACGT codons are present and the
maximum and minimum nonzero counts are unequal. The strongest named endpoint is
`GAG`; the weakest nonzero endpoint is `TGA`.

## Exact Candidate256 Slot Map

Use the extractor's lexical codon order over `ACGT` as the canonical 6-bit
codon coordinate:

```text
digit(A) = 0
digit(C) = 1
digit(G) = 2
digit(T) = 3

codonIndex(x y z) = 16 * digit(x) + 4 * digit(y) + digit(z)
candidate256Slot(codon) = codonIndex(codon)
```

The codon-count payload maps into a 256-slot audit vector as:

```text
candidate256CodonCount[candidate256Slot(c)] = CDS count(c)
candidate256CodonCount[j] = 0 for 64 <= j < 256
```

This is an injective carrier embedding from the 64-codon space into the first
64 Candidate256 slots. It is not a scale map, not a unit map, and not a
`Candidate256PhysicalCalibrationExternalReceipt` field.

Complete slot map:

| Codon | Slot | Codon | Slot | Codon | Slot | Codon | Slot |
|---|---:|---|---:|---|---:|---|---:|
| `AAA` | 0 | `AAC` | 1 | `AAG` | 2 | `AAT` | 3 |
| `ACA` | 4 | `ACC` | 5 | `ACG` | 6 | `ACT` | 7 |
| `AGA` | 8 | `AGC` | 9 | `AGG` | 10 | `AGT` | 11 |
| `ATA` | 12 | `ATC` | 13 | `ATG` | 14 | `ATT` | 15 |
| `CAA` | 16 | `CAC` | 17 | `CAG` | 18 | `CAT` | 19 |
| `CCA` | 20 | `CCC` | 21 | `CCG` | 22 | `CCT` | 23 |
| `CGA` | 24 | `CGC` | 25 | `CGG` | 26 | `CGT` | 27 |
| `CTA` | 28 | `CTC` | 29 | `CTG` | 30 | `CTT` | 31 |
| `GAA` | 32 | `GAC` | 33 | `GAG` | 34 | `GAT` | 35 |
| `GCA` | 36 | `GCC` | 37 | `GCG` | 38 | `GCT` | 39 |
| `GGA` | 40 | `GGC` | 41 | `GGG` | 42 | `GGT` | 43 |
| `GTA` | 44 | `GTC` | 45 | `GTG` | 46 | `GTT` | 47 |
| `TAA` | 48 | `TAC` | 49 | `TAG` | 50 | `TAT` | 51 |
| `TCA` | 52 | `TCC` | 53 | `TCG` | 54 | `TCT` | 55 |
| `TGA` | 56 | `TGC` | 57 | `TGG` | 58 | `TGT` | 59 |
| `TTA` | 60 | `TTC` | 61 | `TTG` | 62 | `TTT` | 63 |

Under this map:

```text
GAG -> slot 34 -> count 867771
TGA -> slot 56 -> count 8978
```

These two slots are enough to witness nontrivial codon-frequency separation
inside the Candidate256 carrier namespace.

## Boundary

Allowed use:

- cite the packet as checksum-bound Drosophila Release 6 source evidence
- cite the CDS codon witness as nonuniform
- use `slot 34` and `slot 56` as named Candidate256 carrier endpoints for a
  nontrivial witness/request surface
- request an external provider to decide whether any physical calibration,
  chemistry law, or dimensional interpretation can be supplied

Disallowed use:

- do not treat raw codon counts as physical units
- do not treat the 64-to-256 injection as `candidate256SurrogateScale`
- do not construct or imply `Candidate256PhysicalCalibrationAuthorityToken`
- do not construct or imply `Candidate256PhysicalCalibrationExternalReceipt`
- do not promote W4, chemistry recovery, biology recovery, Brain recovery, or
  unification from this packet

