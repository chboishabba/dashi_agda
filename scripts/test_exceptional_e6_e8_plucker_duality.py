#!/usr/bin/env python3
from exceptional_e6_e8_plucker_duality import compute_receipt


def main() -> None:
    r = compute_receipt()
    assert r["matrix_rank"] == 5
    assert r["gram_identity"] is True
    assert r["gram_scalar"] == 2
    assert r["symplectic_projective_points"] == 40
    assert r["symplectic_isotropic_lines"] == 40
    assert r["e6_null_projective_points"] == 40
    assert r["distinct_e6_images"] == 40
    assert r["all_images_null"] is True
    assert r["image_equals_null_quadric"] is True
    assert r["pairwise_incidence_checked"] is True
    assert r["line_intersection_iff_e6_orthogonality"] is True


if __name__ == "__main__":
    main()
