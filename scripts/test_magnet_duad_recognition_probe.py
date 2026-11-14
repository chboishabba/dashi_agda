from magnet_duad_recognition_probe import (
    duads,
    rank3_orbit_sizes,
    raw_axis_support_closed_under_c3,
    phase_line_pair_orbit_profile,
)


def test_duad_carrier_count_and_rank3_partition():
    assert len(duads()) == 276
    assert rank3_orbit_sizes() == (1, 44, 231)


def test_raw_real_axis_support_is_not_c3_stable():
    assert raw_axis_support_closed_under_c3() is False


def test_phase_resolved_pair_orbits():
    assert phase_line_pair_orbit_profile() == {
        "C3": {3: 210},
        "C3xC2": {3: 78, 6: 66},
    }


if __name__ == "__main__":
    test_duad_carrier_count_and_rank3_partition()
    test_raw_real_axis_support_is_not_c3_stable()
    test_phase_resolved_pair_orbits()
    print("ok")
