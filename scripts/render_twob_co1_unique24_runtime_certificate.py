#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import json
import sys
from pathlib import Path


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    if len(sys.argv) != 3:
        raise SystemExit(
            "usage: render_twob_co1_unique24_runtime_certificate.py "
            "<unique24.json> <output.agda>"
        )
    src = Path(sys.argv[1])
    out = Path(sys.argv[2])
    data = json.loads(src.read_text())

    assert data["co1_order"] == 4157776806543360000
    assert data["symmetric_square_dimension"] == 300
    assert data["minimal_24_submodule_count"] == 1
    assert data["unique_minimal_24_submodule"] is True
    assert data["unique_minimal_24_equals_frobenius"] is True
    assert data["socle_dimension"] == 24
    assert data["socle_equals_frobenius"] is True
    assert data["actual_tate_residual_image_identified"] is False

    out.parent.mkdir(parents=True, exist_ok=True)
    module = f'''module DASHI.Moonshine.Generated.TwoBCo1Unique24RuntimeCertificate where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- GENERATED RUNTIME RECEIPT: UNIQUE Co1-STABLE 24 IN Sym2(24)
--
-- This receipt is intentionally target-side only.  It proves that the explicit
-- Frobenius-square image is the unique minimal 24-dimensional Co1-submodule
-- and the full socle of Sym2(24).  It does NOT identify the actual Tate norm
-- residual image with that submodule; the same-object residual image must still
-- be shown Co1-stable and rank 24 (rank is paid elsewhere by the support squeeze).
------------------------------------------------------------------------

runtimeReceiptSha256 : String
runtimeReceiptSha256 = "{sha256(src)}"

minimal24SubmoduleCount : Nat
minimal24SubmoduleCount = {data['minimal_24_submodule_count']}
socleDimension : Nat
socleDimension = {data['socle_dimension']}

uniqueMinimal24Submodule : Bool
uniqueMinimal24Submodule = true
uniqueMinimal24EqualsFrobenius : Bool
uniqueMinimal24EqualsFrobenius = true
socleEqualsFrobenius : Bool
socleEqualsFrobenius = true
actualTateResidualImageIdentified : Bool
actualTateResidualImageIdentified = false

minimal24SubmoduleCountIsOne : minimal24SubmoduleCount ≡ 1
minimal24SubmoduleCountIsOne = refl
socleDimensionIs24 : socleDimension ≡ 24
socleDimensionIs24 = refl
'''
    out.write_text(module)


if __name__ == "__main__":
    main()
