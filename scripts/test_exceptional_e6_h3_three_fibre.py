#!/usr/bin/env python3
from exceptional_e6_h3_three_fibre import compute_receipt


def main() -> None:
    r = compute_receipt()
    assert r["base_null_a2cube_classes"] == 40
    assert r["h3_patch_count"] == 120
    assert r["patches_per_base_class"] == 3
    assert r["chosen_base_stabilizer_order"] == 1296
    assert r["three_patch_permutation_image_order"] == 6
    assert r["three_patch_permutation_image_is_full_s3"] is True
    assert r["canonical_c3_orientation_from_e6_carrier"] is False


if __name__ == "__main__":
    main()
