#!/usr/bin/env python3
from exceptional_e8_normalizer_vector_image import compute_receipt


def main() -> None:
    r = compute_receipt()
    assert r["normalizer_vector_image_order"] == 103680
    assert r["symplectic_multiplier_plus_one_count"] == 51840
    assert r["antisymplectic_multiplier_minus_one_count"] == 51840
    assert r["other_multiplier_count"] == 0
    assert r["centralizer_order_from_previous_exact_receipt"] == 155520
    assert r["normalizer_order_from_nontrivial_aut_c3_coset"] == 311040


if __name__ == "__main__":
    main()
