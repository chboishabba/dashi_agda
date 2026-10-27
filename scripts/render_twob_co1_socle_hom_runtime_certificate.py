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
            "usage: render_twob_co1_socle_hom_runtime_certificate.py "
            "<socle-hom.json> <output.agda>"
        )
    src=Path(sys.argv[1]); out=Path(sys.argv[2])
    d=json.loads(src.read_text())
    assert d['co1_order']==4157776806543360000
    assert d['sym2_dimension']==300
    assert d['composition_factor_dimensions']==[1,1,24,274]
    assert d['hom_1_to_sym2_dimension']==0
    assert d['hom_24_to_sym2_dimension']==1
    assert d['hom_274_to_sym2_dimension']==0
    assert d['unique_24_hom_rank']==24
    assert d['frobenius_spans_unique_24_hom'] is True
    assert d['socle_forced_single_24'] is True
    assert d['socle_forced_frobenius'] is True
    assert d['actual_tate_residual_image_identified'] is False

    out.parent.mkdir(parents=True,exist_ok=True)
    out.write_text(f'''module DASHI.Moonshine.Generated.TwoBCo1SocleHomRuntimeCertificate where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- GENERATED RUNTIME RECEIPT: Co1 Sym2(24) SOCLE/HOM RIGIDITY
--
-- Composition factors are 1,1,24,274.  There are no simple 1- or 274-
-- submodules, while Hom_Co1(24,Sym2(24)) is one-dimensional and its unique
-- nonzero map is the explicit Frobenius-square embedding.  Hence the socle is
-- exactly one copy of the natural 24 and is literally the Frobenius range.
--
-- Firewall: the actual Tate residual norm image is not identified here.
------------------------------------------------------------------------

runtimeReceiptSha256 : String
runtimeReceiptSha256 = "{sha256(src)}"

hom1ToSym2Dimension : Nat
hom1ToSym2Dimension = 0
hom24ToSym2Dimension : Nat
hom24ToSym2Dimension = 1
hom274ToSym2Dimension : Nat
hom274ToSym2Dimension = 0
unique24HomRank : Nat
unique24HomRank = 24

socleForcedSingle24 : Bool
socleForcedSingle24 = true
socleForcedFrobenius : Bool
socleForcedFrobenius = true
actualTateResidualImageIdentified : Bool
actualTateResidualImageIdentified = false

hom24ToSym2DimensionIsOne : hom24ToSym2Dimension ≡ 1
hom24ToSym2DimensionIsOne = refl
unique24HomRankIs24 : unique24HomRank ≡ 24
unique24HomRankIs24 = refl
''')


if __name__=='__main__':
    main()
