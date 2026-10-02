#!/usr/bin/env python3
from __future__ import annotations

import json
import sys
from pathlib import Path


def b(x: bool) -> str:
    return "true" if x else "false"


def main() -> None:
    if len(sys.argv) != 4:
        raise SystemExit(
            "usage: render_m22_completion10_runtime_certificate.py "
            "<involution.json> <composition.json> <output.agda>"
        )

    involution = json.loads(Path(sys.argv[1]).read_text())
    composition = json.loads(Path(sys.argv[2]).read_text())
    out = Path(sys.argv[3])
    out.parent.mkdir(parents=True, exist_ok=True)

    has_j2x5 = involution["matching_J2x5_row_count"] > 0
    pair_swap_verified_count = sum(
        1
        for rep in involution["representations"]
        for row in rep["involution_classes"]
        if row.get("pair_swap_basis_verified", False)
    )
    has_pair_swap_basis = pair_swap_verified_count > 0
    has_m22_ten = composition["m22_ten_factor_count"] > 0
    has_m22d2_ten = composition["m22d2_ten_factor_count"] > 0

    module = """module DASHI.Moonshine.Generated.M22Completion10RuntimeCertificate where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

------------------------------------------------------------------------
-- GENERATED RUNTIME RECEIPT.
--
-- Inputs:
-- * AtlasRep M22 ten-dimensional GF(2) involution screen;
-- * AtlasRep M24 p276 permutation module restricted to M22:2 and M22.
--
-- This certificate records runtime finite-group/module facts only.
-- It does NOT identify the M24 p276 module with the Carnahan--Urano
-- 2B Tate multiplicity.  That same-object weld remains false below.
------------------------------------------------------------------------

m22TenRepresentationCount : Nat
m22TenRepresentationCount = %(rep_count)d

m22InvolutionRowCount : Nat
m22InvolutionRowCount = %(involution_rows)d

m22J2x5MatchCount : Nat
m22J2x5MatchCount = %(j2x5_count)d

m22HasJ2x5Match : Bool
m22HasJ2x5Match = %(has_j2x5)s

m22FivePairBasisWitnessCount : Nat
m22FivePairBasisWitnessCount = %(pair_swap_count)d

m22HasExplicitFivePairBasis : Bool
m22HasExplicitFivePairBasis = %(has_pair_swap)s

m24PermutationDegree : Nat
m24PermutationDegree = %(perm_degree)d

m22d2Order : Nat
m22d2Order = %(m22d2_order)d

m22Order : Nat
m22Order = %(m22_order)d

m22d2CompositionDimensionSum : Nat
m22d2CompositionDimensionSum = %(m22d2_sum)d

m22CompositionDimensionSum : Nat
m22CompositionDimensionSum = %(m22_sum)d

m22d2TenFactorCount : Nat
m22d2TenFactorCount = %(m22d2_ten)d

m22TenFactorCount : Nat
m22TenFactorCount = %(m22_ten)d

m22d2HasTenFactor : Bool
m22d2HasTenFactor = %(has_m22d2_ten)s

m22HasTenFactor : Bool
m22HasTenFactor = %(has_m22_ten)s

m24PermutationDegreeIs276 : m24PermutationDegree ≡ 276
m24PermutationDegreeIs276 = refl

m22d2CompositionCloses276 : m22d2CompositionDimensionSum ≡ 276
m22d2CompositionCloses276 = refl

m22CompositionCloses276 : m22CompositionDimensionSum ≡ 276
m22CompositionCloses276 = refl

-- Semantic promotion firewall.
sameObjectWithCarnahanUrano2BTate276Paid : Bool
sameObjectWithCarnahanUrano2BTate276Paid = false

completion10EmbeddingIntoActual2BTatePaid : Bool
completion10EmbeddingIntoActual2BTatePaid = false

runtimeM22FactorAndInvolutionEvidenceJointlySufficient : Bool
runtimeM22FactorAndInvolutionEvidenceJointlySufficient =
  %(joint_finite)s
""" % {
        "rep_count": involution["representation_count"],
        "involution_rows": involution["involution_row_count"],
        "j2x5_count": involution["matching_J2x5_row_count"],
        "has_j2x5": b(has_j2x5),
        "pair_swap_count": pair_swap_verified_count,
        "has_pair_swap": b(has_pair_swap_basis),
        "perm_degree": composition["permutation_degree"],
        "m22d2_order": composition["m22d2_order"],
        "m22_order": composition["m22_order"],
        "m22d2_sum": composition["m22d2_dimension_sum"],
        "m22_sum": composition["m22_dimension_sum"],
        "m22d2_ten": composition["m22d2_ten_factor_count"],
        "m22_ten": composition["m22_ten_factor_count"],
        "has_m22d2_ten": b(has_m22d2_ten),
        "has_m22_ten": b(has_m22_ten),
        "joint_finite": b(has_pair_swap_basis and has_m22_ten),
    }

    out.write_text(module)


if __name__ == "__main__":
    main()
