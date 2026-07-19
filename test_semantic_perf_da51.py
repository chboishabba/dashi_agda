#!/usr/bin/env python3

from semantic_perf_da51 import (
    annotate_record,
    classify_file,
    compile_motif_to_fractran,
    erase_annotation,
    mine_semantic_motifs,
    semantic_token,
)


def test_annotation_roundtrip() -> None:
    original = {
        "file": "PerfHistory.agda",
        "counters": {"cycles": 10, "instructions": 20},
        "trace_sha256": "abc",
    }
    annotated = annotate_record(original)
    assert annotated["dashi_class"] == "witness-export"
    assert annotated["dashi_family"] == "witness-family"
    assert erase_annotation(annotated) == original


def test_fractran_precedence() -> None:
    label = classify_file("ActionMonotonicity.agda", has_fractran=True)
    assert label.dashi_class == "fractran-step"
    assert label.dashi_family == "execution-family"


def test_semantic_motif_ignores_surface_counters() -> None:
    rows = []
    for i in range(4):
        rows.extend(
            [
                annotate_record({"file": "PerfHistory.agda", "counters": {"cycles": i}}),
                annotate_record({"file": "ActionMonotonicity.agda", "counters": {"cycles": 100 + i}}),
            ]
        )
    motifs = mine_semantic_motifs(rows, min_len=2, max_len=2, min_support=2)
    assert motifs
    assert motifs[0][0] == semantic_token(rows[0])
    assert motifs[0][1] == semantic_token(rows[1])


def test_compile_motif_to_fractran() -> None:
    records = [
        annotate_record({"file": "PerfHistory.agda"}),
        annotate_record({"file": "ActionMonotonicity.agda"}),
    ]
    motif = tuple(semantic_token(record) for record in records)
    fractions = compile_motif_to_fractran(motif)
    assert len(fractions) == 5
    assert fractions[0].meaning == "reuse promoted semantic motif"
    assert fractions[3].meaning == "MDL-gated semantic motif promotion"
    assert all(f.numerator > 0 and f.denominator > 0 for f in fractions)


if __name__ == "__main__":
    test_annotation_roundtrip()
    test_fractran_precedence()
    test_semantic_motif_ignores_surface_counters()
    test_compile_motif_to_fractran()
    print("semantic perf/DA51 tests: ok")
