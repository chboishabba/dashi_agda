#!/usr/bin/env python3
"""Read-only GenBank symmetry/codec audit on real CAGT source records.

Reuse DASHI's operational UV and four-way lift functions rather than
reimplementing them. Match the Agda DNAFirstFormalism and DNACarrierFibre
quotient (A/T vs C/G) and complement-phase presentations.

No DNA bases, alignments, gene identities, design parameters or experimental
protocols are emitted. No biological-function or chemical energy claims.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
from collections import Counter
from io import StringIO
from pathlib import Path

from Bio import SeqIO
from scripts.genbank_readonly_ingest import parse_genbank_bytes
from scripts.gen_dna_chemistry_E_seq import (
    encode_uv, four_way_details, reverse_complement,
)

SCHEMA = "dashi.dna-genbank-symmetry-observation.v1"
PAIR_PHASE = {
    "A": ("atPair", "primaryPhase"),
    "T": ("atPair", "mirrorPhase"),
    "C": ("cgPair", "primaryPhase"),
    "G": ("cgPair", "mirrorPhase"),
}
INVERSE_PAIR_PHASE = {v: k for k, v in PAIR_PHASE.items()}
COMP = str.maketrans("ACGT", "TGCA")
REFERENCE = "IID-with-observed-single-base-composition; not an empirical null test"


def palindrome_counts_circular(s: str, lengths=(6, 8, 10, 12)) -> dict:
    """Count circular substrings whose word equals its reverse complement."""
    n = len(s)
    out = {}
    for k in lengths:
        if k <= 0 or k % 2 != 0:
            raise ValueError("use positive even palindrome lengths")
        matches = 0
        for start in range(n):
            if all(s[(start + j) % n] == s[(start + k - 1 - j) % n].translate(COMP)
                   for j in range(k // 2)):
                matches += 1
        out[str(k)] = matches
    return out


def four_way_energy(sequence: str, window=256, levels=4) -> dict:
    """Existing UV quad detail energy; not a physical binding energy."""
    if window % (4 ** levels):
        raise ValueError("window must be divisible by four-way lift depth")
    totals = [0.0] * levels
    count = len(sequence) // window
    for offset in range(0, count * window, window):
        uv = encode_uv(sequence[offset:offset + window])
        for channel in uv:
            details, _ = four_way_details(channel, levels)
            for j, detail in enumerate(details):
                totals[j] += float((detail ** 2).sum())
    return {
        "window": window,
        "levels": levels,
        "full_windows": count,
        "trailing_bases_unincluded": len(sequence) % window,
        "squared_detail_energy_per_base":
            [round(v / (count * window), 8) if count else 0.0
             for v in totals],
        "energy_is_chemical_or_biological_measurement": False,
    }


def audit_genbank_symmetry(original: bytes, source_ref: str) -> dict:
    report = parse_genbank_bytes(original, source_ref=source_ref)
    source = SeqIO.read(StringIO(original.decode("utf-8")), "genbank")
    s = str(source.seq).upper()
    if not s or set(s) - set(PAIR_PHASE):
        raise ValueError("expected concrete CAGT string")

    # Exact base -> (chemical-pair quotient, complement phase) decomposition.
    quotient_phase = [PAIR_PHASE[b] for b in s]
    assert "".join(INVERSE_PAIR_PHASE[q] for q in quotient_phase) == s
    assert all(
        PAIR_PHASE[b.translate(COMP)][0] == pair
        and PAIR_PHASE[b.translate(COMP)][1] != phase
        for b, (pair, phase) in zip(s, quotient_phase)
    )
    rc = reverse_complement(s)
    assert reverse_complement(rc) == s

    counts = Counter(s)
    n = len(s)
    freq = {k: counts[k] / n for k in ("A", "C", "G", "T")}
    pair_probability = 2 * (
        freq["A"] * freq["T"] + freq["C"] * freq["G"]
    )
    lengths = (6, 8, 10, 12)
    obs = palindrome_counts_circular(s, lengths)
    expected = {
        str(k): round(n * pair_probability ** (k // 2), 2)
        for k in lengths
    }
    assert obs == palindrome_counts_circular(s[1:] + s[:1], lengths)

    return {
        "schema": SCHEMA,
        "source_ref": source_ref,
        "source_raw_sha256": hashlib.sha256(original).hexdigest(),
        "normalized_sequence_sha256": report["molecule"]["sequence_sha256"],
        "length": n,
        "topology": report["molecule"]["topology"],
        "feature_count": report["feature_count"],
        "base_counts": {k: counts[k] for k in ("A", "C", "G", "T")},
        "chemical_pair_counts": {
            "atPair": counts["A"] + counts["T"],
            "cgPair": counts["C"] + counts["G"],
        },
        "gc_fraction": round((counts["G"] + counts["C"]) / n, 6),
        "base_fibre_decode_encode_identity": True,
        "complement_preserves_chemical_pair_flips_phase": True,
        "reverse_complement_involutive": True,
        "whole_sequence_reverse_complement_equal": s == rc,
        "whole_circular_sequence_dihedral_reflection": rc in (s + s),
        "circular_reverse_complement_palindromes": obs,
        "single_base_iid_reference_expected_counts": expected,
        "reference_hypothesis": REFERENCE,
        "circular_palindrome_counts_rotation_invariant": True,
        "four_way_uv_structural_detail": four_way_energy(s),
        "observations_are_biological_function_evidence": False,
        "energy_is_measured_physical_free_energy": False,
        "protein_identity_or_strain_phenotype_verified": False,
        "source_bases_exported": False,
        "original_source_bytes_rewritten": False,
        "Agda_kernel_proof_of_this_source": False,
    }


def main() -> int:
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("source", type=Path)
    cli.add_argument("--source-ref", default="file-backed-original")
    cli.add_argument("--output", type=Path)
    args = cli.parse_args()
    report = audit_genbank_symmetry(
        args.source.read_bytes(), source_ref=args.source_ref
    )
    result = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(result, encoding="utf-8")
    else:
        print(result, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
