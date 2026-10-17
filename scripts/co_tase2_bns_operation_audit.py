"""Fail-closed BNS 194.268 same-object audit.

Input is an independently acquired JSON operation table.  This script never
manufactures that authority from the existing Gemmi-derived parent operations.
Required JSON schema:
{
  "bns_number": "194.268",
  "bns_symbol": "P6_3'/m'm'c",
  "magnetic_hall_symbol": "-P 6c' 2c",
  "operations": [{"triplet": "x,y,z", "antiunitary": false}, ...]
}

The independent table closes the literal same-object leaf only when its set of
(spatial triplet, antiunitary parity) pairs exactly equals the repository model.
"""
import argparse
import hashlib
import json
from pathlib import Path

from co_tase2_bloch_symmetry import OPS, BNS_NUMBER, BNS_SYMBOL, MAGNETIC_HALL


def modeled_pairs():
    return sorted((g[0].replace(" ", ""), bool(g[6])) for g in OPS)


def audit(path):
    path = Path(path)
    raw = path.read_bytes()
    data = json.loads(raw)
    for key, expected in (
        ("bns_number", BNS_NUMBER),
        ("bns_symbol", BNS_SYMBOL),
        ("magnetic_hall_symbol", MAGNETIC_HALL),
    ):
        if data.get(key) != expected:
            raise ValueError(f"{key}: expected {expected!r}, got {data.get(key)!r}")
    ops = data.get("operations")
    if not isinstance(ops, list):
        raise ValueError("operations must be a list")
    independent = sorted((str(o["triplet"]).replace(" ", ""), bool(o["antiunitary"])) for o in ops)
    modeled = modeled_pairs()
    missing = sorted(set(independent) - set(modeled))
    extra = sorted(set(modeled) - set(independent))
    exact = independent == modeled
    receipt = {
        "authority_sha256": hashlib.sha256(raw).hexdigest(),
        "bns_number": BNS_NUMBER,
        "independent_operation_count": len(independent),
        "modeled_operation_count": len(modeled),
        "exact_operation_table_match": exact,
        "missing_from_model": missing,
        "extra_in_model": extra,
    }
    if not exact:
        raise AssertionError(json.dumps(receipt, indent=2))
    return receipt


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("independent_bns_json")
    p.add_argument("--receipt")
    a = p.parse_args()
    result = audit(a.independent_bns_json)
    if a.receipt:
        Path(a.receipt).write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
