#!/usr/bin/env python3
from exceptional_e8_same_object_symplectic import compute_receipt


def main() -> None:
    r = compute_receipt()
    assert r["det_one_minus_w"] == 81
    assert r["rank_one_minus_w_mod3"] == 4
    assert r["quotient_map_rank"] == 4
    assert r["quotient_map_kills_one_minus_w"] is True
    assert r["quotient_map_is_w_invariant"] is True
    assert r["section_is_right_inverse"] is True
    assert r["kernel_index_equals_image_index"] is True
    assert r["same_object_kernel_identification"] is True
    assert r["alternating_form_descends_left"] is True
    assert r["alternating_form_descends_right"] is True
    assert r["descended_form_is_standard_symplectic"] is True
    assert r["root_count"] == 240
    assert r["nonzero_quotient_classes_hit"] == 80
    assert r["roots_per_nonzero_class"] == 3
    assert r["order_three_orbits"] == 80
    assert r["each_w_orbit_is_one_quotient_class"] is True
    assert r["distinct_orbits_give_distinct_classes"] is True


if __name__ == "__main__":
    main()
