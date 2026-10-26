#!/usr/bin/env python3
"""Exact noncanonicity regression for the existing PR #1250 720/729 D4 map.

Runs the original existing mixed-eight constructor instead of inventing a
new Atlas D4 model. The finite combinatorics are repository-derived.
Original mathematics: orbit-stabilizer and equivariant G-sets (classical);
actual GF3 source D4 words and E+E quotient: PR #1098/ATLAS.
"""
from math import comb
from monster_3b_pointed720729_mixed_d4_eight_ten_quotient import build

def main():
    r=build()
    assert r["quotient80_source_orbits"]=={
        "axis_four":4,"diagonal_four":4,"free_eight":6}
    assert r["all_equivariant_quotient_count"]==2**8*8**6==67108864
    assert r["exact_balanced_equivariant_quotient_count"]==(
        comb(6,3)*(2**8)*(4**6))==20971520
    assert r["balanced_count_independent_stabilizer_formula"]==20971520
    assert r["equivariant_target_automorphism_count"]==4
    assert r["balanced_mod_target_automorphisms"]==5242880
    assert r["per_target_fibre_cardinalities"]==[10]*8
    assert r["outer_orbit_sizes"]=={8:78,4:24}
    assert r["untwisted_mixed8_sheet10_inner9_orbits"]=={4:60,8:60}
    assert r["trivial_sheet_outer720_orbit_census_contradicts_source"] is True
    assert r["classwise_characters"]["identity"]["all729"]==729
    assert r["nontrivial_ten_sheet_D4_twisting_required"] is True
    assert r["full_Heisenberg_equivariance_proved"] is False
    assert r["actual_Monster_normalizer_intertwiner_proved"] is False
    print("PASS: 67,108,864 D4 maps; 20,971,520 balanced; 5,242,880 target-orbits")

if __name__=="__main__":
    main()
