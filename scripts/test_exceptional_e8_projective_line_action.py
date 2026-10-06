#!/usr/bin/env python3
from exceptional_e8_projective_line_action import compute_receipt


def main() -> None:
    r=compute_receipt()
    assert r["symplectic_lines"] == 40
    assert r["sp4_order"] == 51840
    assert r["projective_kernel_order"] == 2
    assert r["projective_kernel_is_plus_minus_identity"] is True
    assert r["effective_line_action_order"] == 25920
    assert r["centralizer_line_action_is_index_two_vs_51840_e6_null_action"] is True


if __name__ == "__main__": main()
