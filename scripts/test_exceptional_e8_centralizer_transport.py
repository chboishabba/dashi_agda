#!/usr/bin/env python3
from exceptional_e8_centralizer_transport import compute_receipt


def main() -> None:
    r=compute_receipt()
    assert r["e8_weyl_order"] == 696729600
    assert r["conjugacy_orbit_size"] == 4480
    assert r["centralizer_order_orbit_stabilizer"] == 155520
    assert r["both_words_commute_with_w"] is True
    assert r["transport_generators_are_symplectic"] is True
    assert r["transport_image_order"] == 51840
    assert r["lift_generated_order"] == 155520
    assert r["lift_is_full_centralizer_by_order"] is True
    assert r["kernel_order"] == 3
    assert r["kernel_is_exactly_w_cyclic"] is True
    assert r["all_transport_fibres_size"] == 3
    assert r["exact_sequence_computationally_closed"] is True


if __name__ == "__main__":
    main()
