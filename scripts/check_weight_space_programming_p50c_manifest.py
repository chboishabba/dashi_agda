#!/usr/bin/env python3
"""Source-manifest consistency oracle for MIT CSAIL WSP experiment 8 / p50c.

Only validates pinned public metadata and independent finite algebra.
It neither loads nor edits Qwen and is not Agda kernel acceptance.
External authors: Rikiya Takehi, Jayden Teoh, Alex Zhang, Omar Khattab.
Original data: RikiyaT/lm_understand-logs@4d09ba6d6a7e891dd8063974dfe81b3d78e3494f
Data CC BY 4.0; this checker is an independent DASHI source check.
"""

import json
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / "Docs" / "fixtures"
PATCH = FIXTURES / "WeightSpaceProgrammingP50CEditManifest.json"
FROZEN = FIXTURES / "WeightSpaceProgrammingP50CFrozenWeightsManifest.json"

BASE_TENSORS = {
    "15": "model.language_model.layers.15.mlp.down_proj.weight",
    "19": "model.language_model.layers.19.mlp.down_proj.weight",
}


def validate_manifests():
    edit = json.loads(PATCH.read_text(encoding="utf-8"))
    frozen = json.loads(FROZEN.read_text(encoding="utf-8"))
    tensors = edit["tensors"]
    assert len(tensors) == edit["changed_tensors"] == 2
    assert set(frozen) == set(BASE_TENSORS)
    by_name = {item["name"]: item for item in tensors}
    assert set(by_name.values()) if False else True  # no implicit hash equality claim
    assert set(by_name) == set(BASE_TENSORS.values())

    touched = 0
    changed = 0
    for layer, name in BASE_TENSORS.items():
        meta = by_name[name]
        selection = frozen[layer]
        cols = selection["selected_neurons"]
        assert selection["name"] == name
        assert meta["shape"] == selection["shape"] == [1024, 3584]
        assert meta["dtype"] == "bfloat16"
        assert meta["form"] == "sparse"
        assert meta["changed_columns"] == len(cols) == 64
        assert len(cols) == len(set(cols))
        assert all(isinstance(col, int) and 0 <= col < 3584 for col in cols)
        assert selection["changed_values"] == 1024 * 64
        assert meta["changed_entries"] <= selection["changed_values"]
        assert meta["changed_rows"] <= 1024
        assert len(meta["base_sha256"]) == len(meta["edited_sha256"]) == 64
        assert meta["base_sha256"] != meta["edited_sha256"]
        touched += selection["changed_values"]
        changed += meta["changed_entries"]

    assert touched == 131_072
    assert changed == edit["changed_entries_total"] == 130_188
    assert touched - changed == 884
    assert Fraction(touched * 100, 800_000_000) == Fraction(2048, 125000)
    return touched, changed


def project(u, w):
    """Exact rational toy projector, not an assertion about the real patch."""
    norm = sum(x * x for x in u)
    assert norm != 0
    coeff = sum(x * y for x, y in zip(u, w)) / norm
    return tuple(y - coeff * x for x, y in zip(u, w))


def validate_toy_projection():
    for u in ((Fraction(1), Fraction(0)),
              (Fraction(3), Fraction(4)),
              (Fraction(-2), Fraction(5))):
        for w in ((Fraction(7), Fraction(-2)),
                  (Fraction(1, 3), Fraction(11, 5)),
                  (Fraction(0), Fraction(0))):
            out = project(u, w)
            assert sum(x * y for x, y in zip(u, out)) == 0
            assert project(u, out) == out


def validate_selectivity():
    selected = {("15", 2), ("19", 5)}
    values = {("15", 2): (4, 9), ("15", 3): (8, 7),
              ("19", 5): (3, 6), ("20", 2): (1, 5)}
    def patch(row):
        return {key: ((0, value[1]) if key in selected else value)
                for key, value in row.items()}
    edited = patch(values)
    assert edited[("15", 2)] == (0, 9)
    assert edited[("19", 5)] == (0, 6)
    assert edited[("15", 3)] == values[("15", 3)]
    assert edited[("20", 2)] == values[("20", 2)]
    assert patch(edited) == edited


if __name__ == "__main__":
    addressed, actual = validate_manifests()
    validate_toy_projection()
    validate_selectivity()
    print(f"PASS: source manifest addressed={addressed}; BF16-different={actual}; "
          f"rounded-back={addressed - actual}")
    print("PASS: exact-rational projector and finite masked-edit toy invariants")
    print("NOT CHECKED: original checkpoint bytes, Agda kernel, Qwen runtime, benchmarks")
