#!/usr/bin/env python3
from exceptional_e8_order3_quotient import compute_receipt


def main() -> None:
    r = compute_receipt()
    assert r["cartan_determinant"] == 1
    assert r["root_count"] == 240
    assert r["fixed_roots"] == 0
    assert r["order_three_orbits"] == 80
    assert r["orbit_size"] == 3
    assert r["det_one_minus_w"] == 81
    assert r["smith_diagonal"] == (1, 1, 1, 1, 3, 3, 3, 3)
    assert r["quotient_order"] == 81
    assert r["nonzero_quotient_classes_hit_by_roots"] == 80
    assert r["roots_per_nonzero_class"] == 3
    assert r["all_root_orbits_distinct_mod_image"] is True


if __name__ == "__main__":
    main()
