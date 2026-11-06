#!/usr/bin/env python3
"""Independent *source-level* finite audit of Gielis/Base369 Agda tables.

This enumerates the literal Agda equations/cases; it DOES NOT elaborate or
type-check them and MUST NOT be promoted to an Agda --safe kernel receipt.
Pure Python standard library; called by check_gielis_base369_cut.sh.
"""
from __future__ import annotations
import hashlib
import json
import math
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
FILES = (
    "DASHI/Geometry/GielisBase369FiniteExact.agda",
    "DASHI/Geometry/GielisBase369NyquistPhase36Exact.agda",
    "DASHI/Geometry/GielisBase369ExistingOwnersWeldExact.agda",
    "Docs/support/reference/GielisBase369Roadmap.md",
    "Docs/support/reference/GielisBase369ProofTheorems.md",
    "scripts/gielis_base369_experiments.py",
    "DASHI/Geometry/GielisBishopPolynomialExact.agda",
)
THEOREMS = (
    "rotation3PreservesSignal", "rotation6PreservesSignal",
    "rotation9PreservesSignal", "reflection3PreservesSignal",
    "reflection6PreservesSignal", "reflection9PreservesSignal",
    "reflectionInvolutive", "rotation3Order",
    "rotation6Order", "rotation9Order",
    "rotate3InverseLeft", "rotate6InverseLeft", "rotate9InverseLeft",
    "rotate3InverseRight", "rotate6InverseRight", "rotate9InverseRight",
    "reflectRotate3", "reflectRotate6", "reflectRotate9",
)


def integer(term: str) -> int:
    term = term.strip()
    positive = re.fullmatch(r"\+\s+(\d+)", term)
    if positive:
        return int(positive.group(1))
    negative = re.fullmatch(r"-\[1\+\s*(\d+)\s*\]", term)
    if negative:
        return -1-int(negative.group(1))
    raise AssertionError(f"not a literal Agda integer: {term!r}")


def table(source: str, name: str, prefix: str, count: int) -> tuple[int, ...]:
    rows = [
        (int(index), integer(term)) for index,term in re.findall(
            rf"^{re.escape(name)} {re.escape(prefix)}-(\d+) = (.+)$",
            source,flags=re.MULTILINE,
        )
    ]
    assert len(rows)==count, (name,len(rows),count)
    assert [i for i,_ in rows] == list(range(count)),name
    return tuple(value for _,value in rows)


def source_audit(root: Path = ROOT) -> dict:
    source = {path:(root/path).read_text() for path in FILES}
    agda=source[FILES[0]]
    ny=source[FILES[1]]
    assert not any(
        re.search(r"(^|\s)postulate(\s|$)|\{\!|--unsafe|--no-termination-check", source[path],flags=re.M)
        for path in (FILES[0],FILES[1],FILES[2],FILES[-1])
    ), "source contains trust escape"

    sig={m:table(agda,f"signal{m}","Phase.p18",18) for m in (3,6,9)}
    assertions=0
    for m,vec in sig.items():
        for j in range(18):
            assert vec[j]==round(2*math.cos(2*math.pi*m*j/18))
            assert vec[(j+18//m)%18]==vec[j]
            assert vec[(18-j)%18]==vec[j]
            assertions+=3

    def dot(x,y): return sum(a*b for a,b in zip(x,y,strict=True))
    gram=[[dot(sig[a],sig[b]) for b in (3,6,9)] for a in (3,6,9)]
    assert gram==[[36,0,0],[0,36,0],[0,0,72]]

    c9=table(ny,"cosNine","p36",36)
    s9=table(ny,"sinNine","p36",36)
    s27=table(ny,"sinTwentySeven","p36",36)
    embedding=[(int(a),int(b)) for a,b in re.findall(
        r"^even18To36 Phase\.p18-(\d+) = p36-(\d+)$",ny,flags=re.M
    )]
    assert embedding==[(j,2*j) for j in range(18)]
    for j in range(18):
        assert s9[2*j]==s27[2*j]==0
        assertions+=2
    assert (s9[1],s27[1])==(1,-1)
    for j in range(36):
        assert c9[j]==(1,0,-1,0)[j%4]
        assert s9[j]==(0,1,0,-1)[j%4]
        assert s27[j]==(0,-1,0,1)[j%4]
        assertions+=3

    for theorem in THEOREMS:
        cases=[int(j) for j in re.findall(
            rf"^{re.escape(theorem)} Phase\.p18-(\d+) = refl$",
            agda,flags=re.M
        )]
        assert cases==list(range(18)),(theorem,cases)
        assertions+=18

    roadmap=source[FILES[3]]
    gates=re.findall(r"^\| (G\d\d) \|",roadmap,flags=re.M)
    assert gates==[f"G{i:02d}" for i in range(1,22)]
    for phase in range(6): assert f"P{phase}" in roadmap
    for deliverable in range(8): assert f"D{deliverable}" in roadmap

    proof=source[FILES[4]]
    for i in range(1,20):
        assert f"E{i:02d} —" in proof
    ray=source[FILES[5]]
    for token in (
        "wall_delta_p = d-new_d","ray_delta_p = -wall_delta_p",
        "ideal_specular_wall_torque_nm","include_controls",
        "model_encode","nyquist36_receipt",
    ):
        assert token in ray,token

    return {
        "status":"source_enumeration_passed",
        "scope":"literal Agda tables, 18-clause coverage, links and source markers",
        "finite_checks":assertions,
        "gram_369":gram,
        "complete_18_case_theorems":len(THEOREMS),
        "nyquist_fine_sample_9":s9[1],
        "nyquist_fine_sample_27":s27[1],
        "roadmap_exact_gates":21,
        "phases":6,
        "deliverables":8,
        "paper_proof_sections":19,
        "file_sha256":{
            path:hashlib.sha256(data.encode()).hexdigest()
            for path,data in source.items()
        },
        "agda_kernel_accepted":False,
        "python_test_suite_executed_by_this_script":False,
        "physical_kozyrev_scene_parity":False,
    }


if __name__ == "__main__":
    print(json.dumps(source_audit(),indent=2,sort_keys=True))
