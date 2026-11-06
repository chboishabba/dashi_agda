#!/usr/bin/env python3
"""Single-source SI speed-of-light adapter for Gielis/Kozyrev arithmetic.

Reads the EXISTING canonical Agda parsed-carrier value instead of
independently setting c in every Python calculation. A missing or
changed source fails closed. Structural SI exactness of c is separate
from external authority payload acceptance and apparatus calibration.
"""
from __future__ import annotations
from pathlib import Path
import re

ROOT=Path(__file__).resolve().parents[1]
CANONICAL_C_OWNER=(
    ROOT/"DASHI/Promotion/SIExactConstantParsedCarrierRequest.agda")
CANONICAL_SI_OWNER=ROOT/"DASHI/Physics/Units/SI.agda"
EXPECTED_BIPM_C=299792458

def canonical_speed_of_light_si():
    text=CANONICAL_C_OWNER.read_text(encoding="utf-8")
    match=re.search(
        r"canonicalCMetrePerSecondIntegerCarrier\s*:"
        r"\s*ExactIntegerTextCarrier\s*"
        r"canonicalCMetrePerSecondIntegerCarrier\s*=\s*"
        r"record\s*\{\s*sign\s*=\s*positiveSign\s*"
        r";\s*absoluteValue\s*=\s*(\d+)\b",
        text,re.S)
    if not match:
        raise RuntimeError("canonical SI c carrier not source-verified")
    value=int(match.group(1))
    if value!=EXPECTED_BIPM_C:
        raise RuntimeError("canonical SI c integer differs from BIPM definition")
    si=CANONICAL_SI_OWNER.read_text(encoding="utf-8")
    expected={
        "Power":r"dim\s+\(pos 2\)\s+one\s+minusThree\s+zeroI",
        "Force":r"dim\s+one\s+one\s+minusTwo\s+zeroI",
        "Energy":r"dim\s+\(pos 2\)\s+one\s+minusTwo\s+zeroI",
    }
    for name,pattern in expected.items():
        line=re.search(rf"(?m)^{name}\s*=\s*([^\n]+)",si)
        if not line or not re.search(pattern,line.group(1)):
            raise RuntimeError(f"SI {name} dimension changed")
    return value

def owner_receipt():
    return {
        "speed_of_light_m_per_s":canonical_speed_of_light_si(),
        "canonical_owner":str(CANONICAL_C_OWNER.relative_to(ROOT)),
        "si_dimension_owner":str(CANONICAL_SI_OWNER.relative_to(ROOT)),
        "si_power_exponents_MLT":(1,2,-3),
        "si_force_exponents_MLT":(1,1,-2),
        "si_wall_torque_exponents_MLT":(1,2,-2),
        "si_angular_impulse_exponents_MLT":(1,2,-1),
        "torque_is_nominally_not_energy":True,
        "external_authority_payload_promoted":False,
        "apparatus_calibrated":False,
    }

if __name__=="__main__":
    import json
    print(json.dumps(owner_receipt(),indent=2,sort_keys=True))
