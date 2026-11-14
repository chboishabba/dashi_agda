#!/usr/bin/env python3
from exceptional_e8_integer_kernel_constructive import compute_receipt


def main() -> None:
    r=compute_receipt()
    assert r["u_kills_one_minus_w_mod3"] is True
    assert r["mod3_split_identity_A_B_equals_I_minus_R_U"] is True
    assert r["integer_triple_lift_A_C_equals_3I"] is True
    assert r["constructive_kernel_inclusion_closed"] is True
    assert r["image_into_kernel_closed"] is True
    assert r["integer_kernel_equals_image_constructively"] is True


if __name__ == "__main__":
    main()
