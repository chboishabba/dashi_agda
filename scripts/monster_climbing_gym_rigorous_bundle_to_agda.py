#!/usr/bin/env python3
"""Compile verified FLINT/Arb phase-cell rows into an Agda certificate module.

The generated module instantiates `CheckedRigorousWallCertificate` only for
canonical Ogg primes and only when the exact dyadic interval is strictly inside
one native radix cell.  Natural-number inequalities are emitted as concrete
`toWitness` decisions, so the finite cell arithmetic is rechecked by Agda.

The generated external-enclosure metadata remains *external provenance*.  The
compiler does not create a theorem that FLINT is correct or that the enclosed
ordinate is a zeta zero; that separation is part of the target Agda type.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

from monster_climbing_gym_verify_rigorous_bundle import (
    dyadic_interval,
    inferred_unique_cell,
    load_ndjson,
)

LANE = {
    2: "p2", 3: "p3", 5: "p5", 7: "p7", 11: "p11", 13: "p13",
    17: "p17", 19: "p19", 23: "p23", 29: "p29", 31: "p31",
    41: "p41", 47: "p47", 59: "p59", 71: "p71",
}


def normalize_nonnegative_dyadic(obj: dict[str, Any]) -> tuple[int, int, int]:
    lo_m = int(obj["lower_mantissa"])
    hi_m = int(obj["upper_mantissa"])
    e = int(obj["two_exp"])
    if lo_m < 0 or hi_m < 0:
        raise ValueError("Agda DyadicInterval carrier is nonnegative")
    if e >= 0:
        return 0, lo_m << e, hi_m << e
    return -e, lo_m, hi_m


def agda_interval(name: str, obj: dict[str, Any]) -> str:
    k, lo, hi = normalize_nonnegative_dyadic(obj)
    return f"""{name} : Dyadic.DyadicInterval
{name} =
  Dyadic.dyadic-interval {k} {lo} {hi}
    (toWitness {{a? = {lo} ≤? {hi}}} _)
"""


def compile_row(row: dict[str, Any], bundle_hash: str, producer_version: str) -> str | None:
    p = int(row["prime"])
    if p not in LANE or not row.get("fractional_strip_unique") or not row.get("cell_unique"):
        return None
    a = int(row["exponent"])
    n = int(row["zero_index"])
    wall_n = int(row["wall_n"])
    phase_lo, phase_hi = dyadic_interval(row["phase_interval"])
    j = inferred_unique_cell(phase_lo, phase_hi, wall_n)
    if j is None or j != int(row["cell_index"]):
        raise ValueError("row does not pass exact cell inference")

    zk, zlo, zhi = normalize_nonnegative_dyadic(row["zero_ordinate_interval"])
    pk, plo, phi = normalize_nonnegative_dyadic(row["phase_interval"])
    den = 1 << pk
    left_lower = j * den
    right_lower = wall_n * plo
    left_upper = wall_n * phi
    right_upper = (j + 1) * den
    if not (left_lower < right_lower and left_upper < right_upper and j < wall_n):
        raise ValueError("strict cell inequalities failed during Agda compilation")

    stem = f"z{n}-p{p}-a{a}"
    form = f"Gym.wall-form Lane.{LANE[p]} {a}"
    zero_name = f"zero-interval-{stem}"
    phase_name = f"phase-interval-{stem}"
    external_name = f"external-{stem}"
    cell_name = f"cell-{stem}"
    cert_name = f"certificate-{stem}"

    return "\n".join([
        agda_interval(zero_name, row["zero_ordinate_interval"]).rstrip(),
        agda_interval(phase_name, row["phase_interval"]).rstrip(),
        f"""{external_name} : Rigorous.ExternalRigorousPhaseEnclosure ({form})
{external_name} =
  Rigorous.external-rigorous-phase-enclosure
    {n}
    {zero_name}
    {phase_name}
    \"FLINT acb_dirichlet + Arb\"
    \"{producer_version}\"
    \"acb_dirichlet_hardy_z_zero; phase=frac(t*log(p)/(2*pi))\"
    \"sha256:{bundle_hash}\"
    true true true true
""".rstrip(),
        f"""{cell_name} :
  Dyadic.CertifiedDyadicRadixCell
    (Gym.oggPrimeRadixChart Lane.{LANE[p]})
    {a}
    {phase_name}
{cell_name} =
  Dyadic.certified-dyadic-radix-cell
    {j}
    (toWitness {{a? = {j} <? {wall_n}}} _)
    (toWitness {{a? = {left_lower} <? {right_lower}}} _)
    (toWitness {{a? = {left_upper} <? {right_upper}}} _)
""".rstrip(),
        f"""{cert_name} : Rigorous.CheckedRigorousWallCertificate ({form})
{cert_name} =
  Rigorous.checked-rigorous-wall-certificate
    {external_name}
    {cell_name}
""".rstrip(),
    ]) + "\n"


def compile_module(bundle: Path, module_name: str, producer_version: str) -> tuple[str, int, int]:
    metadata, rows = load_ndjson(bundle)
    bundle_hash = hashlib.sha256(bundle.read_bytes()).hexdigest()
    chunks: list[str] = []
    skipped = 0
    for row in rows:
        chunk = compile_row(row, bundle_hash, producer_version)
        if chunk is None:
            skipped += 1
        else:
            chunks.append(chunk)

    header = f"""module {module_name} where

open import DASHI.Core.Prelude
open import Data.Nat.Properties using (_≤?_; _<?_)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Analysis.DyadicPhaseCellCertificateExact as Dyadic
import DASHI.Moonshine.OggSSPClimbingGymRigorousCertificateExact as Rigorous
import DASHI.Moonshine.OggSSPSignedRadixClimbingGymExact as Gym
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane

------------------------------------------------------------------------
-- GENERATED EXTERNAL-CERTIFICATE ADAPTER
-- bundle SHA-256: {bundle_hash}
-- producer metadata: {json.dumps(metadata, sort_keys=True)}
--
-- Every finite cell inequality below is kernel-rechecked.  The external FLINT
-- enclosure remains provenance-bearing input and is not promoted to an Agda
-- proof that the ordinate is a zeta zero.
------------------------------------------------------------------------

"""
    return header + "\n".join(chunks), len(chunks), skipped


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("bundle", type=Path)
    ap.add_argument("output", type=Path)
    ap.add_argument(
        "--module",
        default="DASHI.Moonshine.Generated.OggSSPClimbingGymRigorousPhaseCertificates",
    )
    ap.add_argument("--producer-version", default="see pinned provenance sidecar")
    args = ap.parse_args()

    text, emitted, skipped = compile_module(args.bundle, args.module, args.producer_version)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(text)
    print(json.dumps({
        "module": args.module,
        "output": str(args.output),
        "emitted_ogg_certificates": emitted,
        "skipped_control_or_unresolved_rows": skipped,
        "external_enclosure_promoted_to_agda_zeta_proof": False,
    }, sort_keys=True))


if __name__ == "__main__":
    main()
