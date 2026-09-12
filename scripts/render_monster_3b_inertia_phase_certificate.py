#!/usr/bin/env python3
"""Validate phase-resolved MN3B inertia output and render an Agda receipt.

This renderer is deliberately separate from render_monster_3b_certificate.py:
the older renderer certifies the full-normalizer paired-phase split, while this
one certifies restriction to the centralizer/inertia subgroup and the resulting
zeta/zeta^2 degree split.  It does not construct representation matrices or an
intertwiner.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

EXPECTED = [12, 78]
HEISENBERG_DEGREE = 729


def req_int(d: dict[str, Any], key: str) -> int:
    v = d.get(key)
    if not isinstance(v, int) or isinstance(v, bool):
        raise ValueError(f"{key} must be an integer")
    return v


def validate(payload: dict[str, Any]) -> dict[str, Any]:
    if payload.get("phase_resolution_certified") is not True:
        raise ValueError("phase_resolution_certified must be true")
    degrees = payload.get("phase_resolved_multiplicity_degrees")
    if degrees != EXPECTED:
        raise ValueError("phase_resolved_multiplicity_degrees must be [12, 78]")

    c = req_int(payload, "mn3b_central_class_position")
    z = req_int(payload, "chosen_zeta_central_class_position")
    z2 = req_int(payload, "chosen_zeta_squared_central_class_position")
    if min(c, z, z2) <= 0 or z == z2:
        raise ValueError("central class positions must be positive and phase classes distinct")

    records = payload.get("records")
    if not isinstance(records, list) or len(records) != 2:
        raise ValueError("expected exactly two phase-resolved paired records")

    seen: list[int] = []
    total_zeta = 0
    total_zeta2 = 0
    checksum = 0
    for row in records:
        if not isinstance(row, dict):
            raise ValueError("record must be an object")
        pos = req_int(row, "mn3b_position")
        degree = req_int(row, "mn3b_degree")
        mult = req_int(row, "mn3b_multiplicity")
        zd = req_int(row, "zeta_degree")
        z2d = req_int(row, "zeta_squared_degree")
        md = req_int(row, "multiplicity_degree")
        if min(pos, degree, mult, zd, z2d, md) <= 0:
            raise ValueError("record values must be positive")
        if zd != z2d:
            raise ValueError("zeta/zeta^2 degrees must agree in each paired constituent")
        if zd != HEISENBERG_DEGREE * md:
            raise ValueError("zeta degree must equal 729 times multiplicity degree")
        if degree != zd + z2d:
            raise ValueError("phase degrees must reconstruct MN3B constituent degree")
        seen.extend([md] * mult)
        total_zeta += mult * zd
        total_zeta2 += mult * z2d
        checksum += pos * mult * degree

    if sorted(seen) != EXPECTED:
        raise ValueError("expanded multiplicity degrees are not [12, 78]")
    if total_zeta != 65610 or total_zeta2 != 65610:
        raise ValueError("phase totals must each equal 65610")

    return {
        "central": c,
        "zeta_class": z,
        "zeta2_class": z2,
        "first": EXPECTED[0],
        "second": EXPECTED[1],
        "zeta_total": total_zeta,
        "zeta2_total": total_zeta2,
        "checksum": checksum,
        "inertia_table": str(payload.get("inertia_table", "")),
        "mn3b_table": str(payload.get("mn3b_table", "")),
    }


def agda(values: dict[str, Any], sha256: str) -> str:
    inertia = values["inertia_table"].replace('"', "")
    mn3b = values["mn3b_table"].replace('"', "")
    return f'''module DASHI.Moonshine.Generated.Monster3BInertiaPhaseResolutionCertificate where

-- GENERATED FILE. GAP + CTblLib restricted the paired-phase MN3B constituents
-- to the 3B centralizer/inertia table and separated the two singleton central
-- phases.  This certificate records character-level phase resolution only; it
-- does not construct actual matrices or a same-action intertwiner.

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.String using (String)

inputSHA256 : String
inputSHA256 = "{sha256}"
mn3bTable : String
mn3bTable = "{mn3b}"
inertiaTable : String
inertiaTable = "{inertia}"

mn3bCentralClassPosition : Nat
mn3bCentralClassPosition = {values['central']}
chosenZetaCentralClassPosition : Nat
chosenZetaCentralClassPosition = {values['zeta_class']}
chosenZetaSquaredCentralClassPosition : Nat
chosenZetaSquaredCentralClassPosition = {values['zeta2_class']}

firstMultiplicityDegree : Nat
firstMultiplicityDegree = {values['first']}
secondMultiplicityDegree : Nat
secondMultiplicityDegree = {values['second']}
zetaTotalDegree : Nat
zetaTotalDegree = {values['zeta_total']}
zetaSquaredTotalDegree : Nat
zetaSquaredTotalDegree = {values['zeta2_total']}
recordChecksum : Nat
recordChecksum = {values['checksum']}
phaseResolutionCertified : Bool
phaseResolutionCertified = true

multiplicitySumCertificate : firstMultiplicityDegree + secondMultiplicityDegree ≡ 90
multiplicitySumCertificate = refl
zetaTensorDegreeCertificate : 729 * (firstMultiplicityDegree + secondMultiplicityDegree) ≡ zetaTotalDegree
zetaTensorDegreeCertificate = refl
zetaSquaredTensorDegreeCertificate : 729 * (firstMultiplicityDegree + secondMultiplicityDegree) ≡ zetaSquaredTotalDegree
zetaSquaredTensorDegreeCertificate = refl
phaseTotalsAgree : zetaTotalDegree ≡ zetaSquaredTotalDegree
phaseTotalsAgree = refl
'''


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("input", type=Path)
    p.add_argument("output", type=Path)
    args = p.parse_args()
    raw = args.input.read_bytes()
    payload = json.loads(raw)
    values = validate(payload)
    digest = hashlib.sha256(raw).hexdigest()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(agda(values, digest), encoding="utf-8")
    print(f"validated inertia phase resolution; sha256={digest}")


if __name__ == "__main__":
    main()
