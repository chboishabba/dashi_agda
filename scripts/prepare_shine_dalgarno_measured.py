#!/usr/bin/env python3
"""Adapt the ORIGINAL Shine-Dalgarno dmsC MAVE measurements, not inferred maps.

Upstream: cmarti/shine_dalgarno/data/dmsc.csv, 2026 MBE msag023,
DOI 10.1093/molbev/msag023. Source has Genotype and dmsC.1/.2/.3
replicate columns. Missing replicate values are NOT synthesized.
Deterministic genotype-group splits prevent replicate leakage.
Source file sha256, conversion parameters, split counts retained in manifest.

No download, PNF write, or claim of developmental-attractor calibration.
"""
from __future__ import annotations
import argparse
import csv
import hashlib
import json
import math
from collections import Counter
from pathlib import Path

SOURCE_DOI="10.1093/molbev/msag023"
SAMPLES=("dmsC.1","dmsC.2","dmsC.3")


def normalized_sequence(raw):
    seq=raw.strip().upper().replace("T","U")
    if len(seq)!=9 or any(c not in "ACGU" for c in seq):
        raise ValueError("original MAVE genotype must be a 9-base RNA sequence")
    return seq


def split_for_genotype(seq, salt):
    digest=hashlib.sha256((salt+":"+seq).encode("utf-8")).hexdigest()
    fraction=int(digest[:16],16)/float(16**16)
    return "train" if fraction<0.70 else (
        "validation" if fraction<0.85 else "test")


def convert(raw_path, output_path, manifest_path, *,trait_unit, salt="dashi-2026-v1"):
    if not trait_unit.strip():
        raise ValueError("trait unit/scale must be declared by the data reviewer")
    raw_bytes=Path(raw_path).read_bytes()
    source_sha=hashlib.sha256(raw_bytes).hexdigest()
    with Path(raw_path).open(newline="") as stream:
        reader=csv.DictReader(stream)
        if not set(("Genotype",)+SAMPLES).issubset(reader.fieldnames or ()):
            raise ValueError("original MAVE CSV must have Genotype and dmsC.1/2/3")
        original=list(reader)
    if not original:
        raise ValueError("source file has no observations")
    seen=set()
    output=[]
    for row_index,row in enumerate(original,2):
        seq=normalized_sequence(row["Genotype"])
        if seq in seen:
            raise ValueError("duplicate original genotype; reconcile upstream before split")
        seen.add(seq)
        split=split_for_genotype(seq,salt)
        for col in SAMPLES:
            value=(row.get(col) or "").strip()
            if value.lower() in ("", "nan", "na", "null"):
                continue
            try: measured=float(value)
            except ValueError as e:
                raise ValueError(f"invalid original measurement at row {row_index}") from e
            if not math.isfinite(measured):
                raise ValueError("nonfinite primary assay value")
            output.append({
                "source_id":SOURCE_DOI,"sequence":seq,"split":split,
                "measurement_kind":"measured","trait":format(measured,".17g"),
                "trait_unit":trait_unit,"assay_context":"dmsC Shine-Dalgarno MAVE",
                "measurement_id":f"{seq}/{col}",
            })
    if not output:
        raise ValueError("no directly observed replicates")
    counts=Counter(r["split"] for r in output)
    groups=Counter({seq:split_for_genotype(seq,salt)
                    for seq in seen}.values())
    if min(groups.get(k,0) for k in ("train","validation","test"))==0:
        raise ValueError("one or more genotype splits are empty")
    columns=("source_id","sequence","split","measurement_kind","trait",
             "trait_unit","assay_context","measurement_id")
    with Path(output_path).open("w",newline="") as handle:
        writer=csv.DictWriter(handle,fieldnames=columns)
        writer.writeheader()
        writer.writerows(output)
    manifest={
        "authority":"source-measured-only-unpromoted",
        "source_repository":"https://github.com/cmarti/shine_dalgarno",
        "source_path":"data/dmsc.csv",
        "source_doi":SOURCE_DOI,"original_file_sha256":source_sha,
        "split_salt":salt,
        "train_fraction":0.70,"validation_fraction":0.15,"test_fraction":0.15,
        "unit_or_scale_declared":trait_unit,
        "measured_genotypes":len({x["sequence"] for x in output}),
        "measured_replicates":len(output),
        "replicate_counts":dict(counts),
        "genotype_counts":dict(groups),
        "inferred_values_used":False,"pnf_mutation_performed":False,
    }
    Path(manifest_path).write_text(json.dumps(manifest,sort_keys=True,indent=2)+"\n")
    return manifest


def self_test():
    import tempfile
    import itertools
    with tempfile.TemporaryDirectory() as tmp:
        root=Path(tmp)
        src=root/"dmsc.csv";out=root/"assay.csv";manifest=root/"manifest.json"
        with src.open("w",newline="") as handle:
            writer=csv.writer(handle)
            writer.writerow(("Genotype",)+SAMPLES)
            for xs in itertools.product("ACGU", repeat=4):
                seq="AAAAA"+"".join(xs)
                writer.writerow((seq,0.01*seq.count("G"),"",0.1))
        info=convert(src,out,manifest,trait_unit="synthetic-log-fluorescence")
        assert info["measured_replicates"]==512
        assert info["inferred_values_used"] is False
        assert set(info["genotype_counts"])=={"train","validation","test"}
        with out.open() as f:
            rows=list(csv.DictReader(f))
        assert all(r["measurement_kind"]=="measured" for r in rows)
        by_seq={}
        for row in rows:
            by_seq.setdefault(row["sequence"],set()).add(row["split"])
        assert all(len(v)==1 for v in by_seq.values())
    print("PASS: pinned-primary assay columns, original replicas, deterministic split")
    print("SYNTHETIC SELF-TEST; primary source not downloaded or evaluated")


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--raw",type=Path)
    p.add_argument("--out",type=Path)
    p.add_argument("--manifest",type=Path)
    p.add_argument("--trait-unit",type=str)
    p.add_argument("--salt",default="dashi-2026-v1")
    p.add_argument("--self-test",action="store_true")
    a=p.parse_args()
    if a.self_test: self_test(); return
    if not all((a.raw,a.out,a.manifest,a.trait_unit)):
        p.error("--raw --out --manifest --trait-unit required")
    print(json.dumps(convert(a.raw,a.out,a.manifest,
                             trait_unit=a.trait_unit,salt=a.salt),indent=2))


if __name__=="__main__":
    main()
