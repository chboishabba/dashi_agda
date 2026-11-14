"""Pinned, source-inspected creator GenBank metadata — no source sequence copied."""
import json
from pathlib import Path

DATA = (
    Path(__file__).resolve().parents[1]
    / "docs/biology/data/ThoughtEmporiumMagnetoreceptionGenBankSourceInventory.json"
)


def test_real_source_inventory_is_attributed_and_non_promoting():
    data = json.loads(DATA.read_text(encoding="utf-8"))
    assert data["schema"] == "dashi.genbank.creator-source-observation.v1"
    assert data["source"]["creator"] == "The Thought Emporium / Justin Atkin"
    assert data["source"]["git_blob_sha"] == "0578ad167666789fbfd3faa849a455c25097b90c"
    assert data["source"]["source_commit"] == "f83aaf2b3ada085d02d8a25cfdc4ae32c80fe09d"
    assert data["observed"]["length_sequence_letters"] == 11214
    assert data["observed"]["feature_count"] == 22
    assert data["observed"]["topology"] == "circular"
    assert data["observed"]["alphabet"] == "ACGT"
    assert data["authority_boundary"]["promotion_authority"] is False
    assert data["sequence_bases_redistributed"] is False
    assert data["independent_biological_function_verified"] is False


def test_creator_gene_like_label_is_not_automatically_cds():
    data = json.loads(DATA.read_text(encoding="utf-8"))
    gene_like = [
        row for row in data["features"]
        if row.get("source_label") and "cacna1d" in row["source_label"].lower()
    ]
    assert len(gene_like) == 1
    assert gene_like[0]["type"] == "misc_feature"
    assert gene_like[0]["index"] == 8
    cds = [row for row in data["features"] if row["type"] == "CDS"]
    assert len(cds) == 2
    assert set(row["source_label"] for row in cds) == {'"Factor Xa site"', '"AmpR"'}
    assert gene_like[0]["source_label"] not in {row["source_label"] for row in cds}


def test_source_inventory_preserves_compound_origin_and_complements():
    data = json.loads(DATA.read_text(encoding="utf-8"))
    rows = data["features"]
    assert len([r for r in rows if r["raw_location"].startswith("join(")]) == 1
    assert len([r for r in rows if r["raw_location"].startswith("complement(")]) == 7
    assert sum(1 for r in rows if r["type"] == "promoter") == 2
    assert all(r["qualifier_names"] == ["label", "ApEinfo_revcolor", "ApEinfo_fwdcolor"]
               for r in rows)
