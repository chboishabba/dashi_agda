#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import json
import sys
from pathlib import Path


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    if len(sys.argv) != 7:
        raise SystemExit(
            "usage: render_twob_co1_factorthrough_runtime_certificate.py "
            "<co1-wedge.json> <centralizer-virtual.json> <augmentation-hom.json> "
            "<frobenius-hom.json> <centralizer-decomposition.json> <output.agda>"
        )

    wedge_path = Path(sys.argv[1])
    virtual_path = Path(sys.argv[2])
    hom_path = Path(sys.argv[3])
    frob_path = Path(sys.argv[4])
    decomp_path = Path(sys.argv[5])
    out = Path(sys.argv[6])

    wedge = json.loads(wedge_path.read_text())
    virtual = json.loads(virtual_path.read_text())
    hom = json.loads(hom_path.read_text())
    frob = json.loads(frob_path.read_text())
    decomp = json.loads(decomp_path.read_text())

    # Fail closed: finite Co1 candidate fingerprint.
    assert wedge["exterior_square_dimension"] == 276
    assert wedge["one_274_one_composition_profile"] is True
    assert wedge["trivial_factor_count"] == 2
    assert wedge["atlas_274_factor_count"] == 1
    assert wedge["unidentified_factor_count"] == 0
    assert wedge["actual_2b_tate_identified_with_exterior_square"] is False

    # Odd-class virtual shadow of the actual centralizer ordinary branching.
    assert virtual["passing_pair_count"] > 0
    assert virtual["virtual_24_identity_has_solution"] is True
    assert virtual["virtual_276_identity_has_same_solution"] is True
    assert virtual["integral_norm_exact_sequence_paid"] is False

    # Augmentation-filtration obstruction: once the actual Tate JH profile is
    # 1,274,1 these vanishings force the normal 2^24 action to be trivial.
    assert hom["natural_dimension"] == 24
    assert hom["large_simple_dimension"] == 274
    assert hom["tensor_dimension"] == 24 * 274
    assert hom["hom_24_to_1_dimension"] == 0
    assert hom["hom_24_to_274_dimension"] == 0
    assert hom["hom_24_tensor_274_to_1_dimension"] == 0
    assert hom["hom_24_tensor_274_to_274_dimension"] == 0
    assert hom["all_augmentation_adjacent_homs_vanish"] is True
    assert hom["normal_2pow24_triviality_on_any_1_274_1_filtered_module_forced"] is True

    # Residual 24 -> Sym2(24) rigidity.
    assert frob["natural_dimension"] == 24
    assert frob["symmetric_square_dimension"] == 300
    assert frob["explicit_frobenius_rank"] == 24
    assert frob["hom_24_to_sym2_dimension"] == 1
    assert frob["unique_nonzero_hom_line"] is True
    assert frob["explicit_frobenius_spans_hom"] is True
    assert frob["actual_norm_residual_24_map_identified"] is False
    assert frob["common_98280_map_identified"] is False

    # Actual 2-modular decomposition-matrix content of the centralizer pieces.
    assert decomp["candidate_count"] > 0
    assert decomp["strong_candidate_count"] > 0
    assert decomp["rigid_support_candidate_count"] > 0
    assert decomp["jh_common_98280_plus_residual24_pattern_found"] is True
    assert decomp["common_98280_support_separated_from_residual_lanes"] is True
    assert decomp["actual_norm_map_98280_isomorphism_paid"] is False
    assert decomp["actual_tate_exterior_square_weld_paid"] is False

    # The residual 276 JH profile must agree with the actual Co1 wedge candidate.
    # We only need one rigid candidate with degree support 1/274 and total profile
    # matching two trivial factors plus one 274 factor.
    rigid_profile_match = False
    for c in decomp["rigid_support_candidates"]:
        sparse = c["residual_276_sparse"]
        degree_mults: dict[int, int] = {}
        for _, degree, mult in sparse:
            degree_mults[degree] = degree_mults.get(degree, 0) + mult
        if degree_mults.get(1, 0) == 2 and degree_mults.get(274, 0) == 1 and sum(
            degree * mult for degree, mult in degree_mults.items()
        ) == 276:
            rigid_profile_match = True
            break
    assert rigid_profile_match, decomp

    out.parent.mkdir(parents=True, exist_ok=True)
    module = f'''module DASHI.Moonshine.Generated.TwoBCo1FactorThroughRuntimeCertificate where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- GENERATED RUNTIME RECEIPT: Co1 FACTOR-THROUGH / TATE-COKERNEL MAX-CUT
--
-- Inputs:
--   * actual Atlas Co1 wedge^2(24) modular fingerprint;
--   * executed 2B-centralizer virtual 24/276 Brauer identity;
--   * actual Atlas Co1 augmentation Hom-space computation;
--   * Hom_Co1(24,Sym^2(24)) uniqueness / explicit Frobenius embedding;
--   * actual 2-modular decomposition matrix of 2^(1+24).Co1.
--
-- Together these pay substantially more than the old semisimplified screen:
--   1. the actual Tate quotient has JH profile 1,274,1;
--   2. the normal 2^24 action is forced trivial by the augmentation criterion;
--   3. the residual 24 -> 300 equivariant lane is uniquely the Frobenius-square
--      embedding once known nonzero;
--   4. the common 98280 JH support is separated from the residual lanes.
--
-- The remaining same-object seam is deliberately narrower but still real:
-- prove that the actual norm map identifies the common 98280 extension lane
-- (and hence realizes the nonzero residual 24 map).  Only then may Tate276 be
-- promoted to the actual wedge^2(24)/duad module.
------------------------------------------------------------------------

wedgeReceiptSha256 : String
wedgeReceiptSha256 = "{sha256(wedge_path)}"

virtualIdentityReceiptSha256 : String
virtualIdentityReceiptSha256 = "{sha256(virtual_path)}"

augmentationHomReceiptSha256 : String
augmentationHomReceiptSha256 = "{sha256(hom_path)}"

frobeniusHomReceiptSha256 : String
frobeniusHomReceiptSha256 = "{sha256(frob_path)}"

centralizerDecompositionReceiptSha256 : String
centralizerDecompositionReceiptSha256 = "{sha256(decomp_path)}"

co1WedgeDimension : Nat
co1WedgeDimension = 276

co1TrivialFactorCount : Nat
co1TrivialFactorCount = {wedge['trivial_factor_count']}

co1Factor274Count : Nat
co1Factor274Count = {wedge['atlas_274_factor_count']}

centralizerVirtualIdentityPassingPairCount : Nat
centralizerVirtualIdentityPassingPairCount = {virtual['passing_pair_count']}

centralizerDecompositionRigidCandidateCount : Nat
centralizerDecompositionRigidCandidateCount = {decomp['rigid_support_candidate_count']}

hom24ToSym2Dimension : Nat
hom24ToSym2Dimension = {frob['hom_24_to_sym2_dimension']}

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

residual24HomLineUnique : Bool
residual24HomLineUnique = true

residual24UniqueMapIsFrobenius : Bool
residual24UniqueMapIsFrobenius = true

common98280SupportSeparatedFromResidualLanes : Bool
common98280SupportSeparatedFromResidualLanes = true

-- Final map/extension firewalls.
actualNormCommon98280IsomorphismPaid : Bool
actualNormCommon98280IsomorphismPaid = false

actualNormResidual24MapPaidNonzero : Bool
actualNormResidual24MapPaidNonzero = false

actualTateCo1ExtensionIdentifiedWithWedge2_24 : Bool
actualTateCo1ExtensionIdentifiedWithWedge2_24 = false

actualTateStableQ10Constructed : Bool
actualTateStableQ10Constructed = false

co1WedgeDimensionIs276 : co1WedgeDimension ≡ 276
co1WedgeDimensionIs276 = refl

hom24ToSym2DimensionIsOne : hom24ToSym2Dimension ≡ 1
hom24ToSym2DimensionIsOne = refl
'''
    out.write_text(module)


if __name__ == "__main__":
    main()
