#!/usr/bin/env python3
from exceptional_e8_normalizer_e6_same_action import compute_receipt


def main() -> None:
    r = compute_receipt()
    assert tuple(r["phase_conjugation_permutation_I_w_w2"]) == (0, 2, 1)
    assert r["normalizer_conjugates_w_to_w2"] is True
    assert r["normalizer_multiplier"] == 2
    assert r["symplectic_line_count"] == 40
    assert r["e8_normalizer_projective_group_order"] == 51840
    assert r["e6_null_group_order"] == 51840
    assert r["plucker_bijection_size"] == 40
    assert r["same_ordered_carrier_used"] is True
    assert r["permutation_sets_compared_extensionally"] is True
    assert r["permutation_sets_literally_equal"] is True


if __name__ == "__main__":
    main()
