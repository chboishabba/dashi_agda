#!/usr/bin/env python3
"""Emit a checksum-bound Drosophila Release 6 genome authority packet.

This is a non-promoting evidence extractor.  It binds local NCBI FASTA
artifacts to checksums and computes a coding-sequence codon-frequency witness
from the CDS FASTA.  It does not construct a W4 calibration receipt.
"""

from __future__ import annotations

import argparse
import gzip
import hashlib
import json
from collections import Counter
from pathlib import Path


CODONS = [a + b + c for a in "ACGT" for b in "ACGT" for c in "ACGT"]


def sha256_path(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def fasta_sequences(path: Path):
    opener = gzip.open if path.suffix == ".gz" else open
    name = None
    parts: list[str] = []
    with opener(path, "rt", encoding="utf-8", errors="replace") as f:
        for raw in f:
            line = raw.strip()
            if not line:
                continue
            if line.startswith(">"):
                if name is not None:
                    yield name, "".join(parts).upper()
                name = line[1:]
                parts = []
            else:
                parts.append(line)
        if name is not None:
            yield name, "".join(parts).upper()


def fasta_stats(path: Path) -> dict[str, int]:
    seq_count = 0
    total_bases = 0
    acgt_bases = 0
    ambiguous_bases = 0
    for _name, seq in fasta_sequences(path):
        seq_count += 1
        total_bases += len(seq)
        acgt_bases += sum(1 for ch in seq if ch in "ACGT")
        ambiguous_bases += sum(1 for ch in seq if ch not in "ACGT")
    return {
        "sequence_count": seq_count,
        "total_bases": total_bases,
        "acgt_bases": acgt_bases,
        "ambiguous_or_gap_bases": ambiguous_bases,
    }


def codon_stats(cds_path: Path) -> dict[str, object]:
    counts: Counter[str] = Counter()
    skipped_ambiguous = 0
    skipped_partial = 0
    cds_count = 0
    for _name, seq in fasta_sequences(cds_path):
        cds_count += 1
        limit = len(seq) - (len(seq) % 3)
        skipped_partial += len(seq) - limit
        for i in range(0, limit, 3):
            codon = seq[i : i + 3]
            if all(ch in "ACGT" for ch in codon):
                counts[codon] += 1
            else:
                skipped_ambiguous += 1

    nonzero = {c: counts[c] for c in CODONS if counts[c] > 0}
    min_codon, min_count = min(nonzero.items(), key=lambda kv: (kv[1], kv[0]))
    max_codon, max_count = max(nonzero.items(), key=lambda kv: (kv[1], kv[0]))
    top10 = sorted(nonzero.items(), key=lambda kv: (-kv[1], kv[0]))[:10]
    bottom10 = sorted(nonzero.items(), key=lambda kv: (kv[1], kv[0]))[:10]
    total_codons = sum(counts.values())
    uniform_expected = total_codons / 64 if total_codons else 0.0
    chi_square_uniform = (
        sum(((counts[c] - uniform_expected) ** 2) / uniform_expected for c in CODONS)
        if uniform_expected
        else 0.0
    )

    return {
        "cds_sequence_count": cds_count,
        "total_acgt_codons": total_codons,
        "distinct_acgt_codons": len(nonzero),
        "skipped_ambiguous_codons": skipped_ambiguous,
        "skipped_partial_bases": skipped_partial,
        "max_codon": max_codon,
        "max_codon_count": max_count,
        "min_nonzero_codon": min_codon,
        "min_nonzero_codon_count": min_count,
        "max_min_count_ratio": max_count / min_count,
        "chi_square_vs_uniform_64": chi_square_uniform,
        "top10_codons": [{"codon": c, "count": n} for c, n in top10],
        "bottom10_codons": [{"codon": c, "count": n} for c, n in bottom10],
        "nonuniform_witness": max_count > min_count,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--genomic", type=Path, required=True)
    parser.add_argument("--cds", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    authority_metadata = {
        "assembly_accession": "GCF_000001215.4",
        "assembly_name": "Release 6 plus ISO1 MT",
        "organism": "Drosophila melanogaster",
        "taxid": 7227,
        "ncbi_datasets_url": "https://www.ncbi.nlm.nih.gov/datasets/genome/GCF_000001215.4/",
        "ncbi_ftp_dir": "https://ftp.ncbi.nlm.nih.gov/genomes/all/GCF/000/001/215/GCF_000001215.4_Release_6_plus_ISO1_MT/",
        "release6_reference_doi": "10.1101/gr.185579.114",
        "release6_reference_pubmed": "25589440",
        "rejected_prior_doi": "10.1126/science.1237175",
        "rejected_prior_doi_reason": "not the Drosophila Release 6 reference sequence paper",
    }
    metadata_bytes = json.dumps(
        authority_metadata, sort_keys=True, separators=(",", ":")
    ).encode("utf-8")

    packet = {
        "status": "candidate_authority_and_checksum_bound_selection_non_promoting",
        "authority_metadata": authority_metadata,
        "authority_metadata_sha256": hashlib.sha256(metadata_bytes).hexdigest(),
        "artifacts": {
            "genomic_fasta_gz": {
                "path": str(args.genomic),
                "sha256": sha256_path(args.genomic),
                **fasta_stats(args.genomic),
            },
            "cds_from_genomic_fasta_gz": {
                "path": str(args.cds),
                "sha256": sha256_path(args.cds),
                **fasta_stats(args.cds),
            },
        },
        "codon_frequency_witness": codon_stats(args.cds),
        "claim_boundary": [
            "This packet binds Drosophila Release 6 authority metadata and local FASTA checksums.",
            "The CDS codon frequency witness is non-uniform, but it is not a W4 calibration law.",
            "This packet does not construct Candidate256PhysicalCalibrationAuthorityToken.",
            "This packet does not inhabit Candidate256PhysicalCalibrationExternalReceipt.",
            "This packet does not promote W4, Brain, physics, biology recovery, or unification.",
        ],
    }

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    main()
