#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import json
import sys
from pathlib import Path


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def b(x: bool) -> str:
    return "true" if x else "false"


def main() -> None:
    if len(sys.argv) != 5:
        raise SystemExit(
            "usage: render_twob_co1_factorthrough_runtime_certificate.py "
            "<co1-wedge.json> <centralizer-virtual.json> <augmentation-hom.json> <output.agda>"
        )

    wedge_path = Path(sys.argv[1])
    virtual_path = Path(sys.argv[2])
    hom_path = Path(sys.argv[3])
    out = Path(sys.argv[4])

    wedge = json.loads(wedge_path.read_text())
    virtual = json.loads(virtual_path.read_text())
    hom = json.loads(hom_path.read_text())

    # Fail closed: these are the exact finite hypotheses needed before the
    # representation-theoretic augmentation criterion may be applied.
    assert wedge["exterior_square_dimension"] == 276
    assert wedge["one_274_one_composition_profile"] is True
    assert wedge["trivial_factor_count"] == 2
    assert wedge["atlas_274_factor_count"] == 1
    assert wedge["unidentified_factor_count"] == 0
    assert wedge["actual_2b_tate_identified_with_exterior_square"] is False

    assert virtual["passing_pair_count"] > 0
    assert virtual["virtual_24_identity_has_solution"] is True
    assert virtual["virtual_276_identity_has_same_solution"] is True
    assert virtual["integral_norm_exact_sequence_paid"] is False

    assert hom["natural_dimension"] == 24
    assert hom["large_simple_dimension"] == 274
    assert hom["tensor_dimension"] == 24 * 274
    assert hom["hom_24_to_1_dimension"] == 0
    assert hom["hom_24_to_274_dimension"] == 0
    assert hom["hom_24_tensor_274_to_1_dimension"] == 0
    assert hom["hom_24_tensor_274_to_274_dimension"] == 0
    assert hom["all_augmentation_adjacent_homs_vanish"] is True
    assert hom["normal_2pow24_triviality_on_any_1_274_1_filtered_module_forced"] is True
    assert hom["actual_tate_has_1_274_1_profile_proved"] is False
    assert hom["actual_tate_normal_2pow24_triviality_proved"] is False

    out.parent.mkdir(parents=True, exist_ok=True)
    module = f'''module DASHI.Moonshine.Generated.TwoBCo1FactorThroughRuntimeCertificate where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- GENERATED RUNTIME RECEIPT: Co1 FACTOR-THROUGH MAX-CUT
--
-- Inputs:
--   * actual Atlas Co1 wedge^2(24) modular fingerprint;
--   * executed 2B-centralizer virtual 24/276 Brauer identity;
--   * actual Atlas Co1 augmentation Hom-space computation.
--
-- Their conjunction pays the semisimplified Co1 profile 1+274+1 and the
-- finite hypotheses of the augmentation-filtration criterion forcing the
-- normal 2^24 action to be trivial.  The remaining Co1 extension class is NOT
-- promoted: actual Tate == wedge^2(24) remains false below.
------------------------------------------------------------------------

wedgeReceiptSha256 : String
wedgeReceiptSha256 = "{sha256(wedge_path)}"

virtualIdentityReceiptSha256 : String
virtualIdentityReceiptSha256 = "{sha256(virtual_path)}"

augmentationHomReceiptSha256 : String
augmentationHomReceiptSha256 = "{sha256(hom_path)}"

co1WedgeDimension : Nat
co1WedgeDimension = 276

co1TrivialFactorCount : Nat
co1TrivialFactorCount = {wedge['trivial_factor_count']}

co1Factor274Count : Nat
co1Factor274Count = {wedge['atlas_274_factor_count']}

centralizerVirtualIdentityPassingPairCount : Nat
centralizerVirtualIdentityPassingPairCount = {virtual['passing_pair_count']}

hom24To1Dimension : Nat
hom24To1Dimension = {hom['hom_24_to_1_dimension']}

hom24To274Dimension : Nat
hom24To274Dimension = {hom['hom_24_to_274_dimension']}

hom24Tensor274To1Dimension : Nat
hom24Tensor274To1Dimension = {hom['hom_24_tensor_274_to_1_dimension']}

hom24Tensor274To274Dimension : Nat
hom24Tensor274To274Dimension = {hom['hom_24_tensor_274_to_274_dimension']}

actualTateCo1SemisimplifiedProfileOne274OnePaid : Bool
actualTateCo1SemisimplifiedProfileOne274OnePaid = true

augmentationHomObstructionPaid : Bool
augmentationHomObstructionPaid = true

normal2Pow24ActionForcedTrivialByCriterion : Bool
normal2Pow24ActionForcedTrivialByCriterion = true

actualTateFactorsThroughCo1ByCriterion : Bool
actualTateFactorsThroughCo1ByCriterion = true

-- Final extension/same-object firewalls.
actualTateCo1ExtensionIdentifiedWithWedge2_24 : Bool
actualTateCo1ExtensionIdentifiedWithWedge2_24 = false

actualTateStableQ10Constructed : Bool
actualTateStableQ10Constructed = false

co1WedgeDimensionIs276 : co1WedgeDimension ≡ 276
co1WedgeDimensionIs276 = refl
'''
    out.write_text(module)


if __name__ == "__main__":
    main()
