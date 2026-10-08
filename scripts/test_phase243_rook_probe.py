from phase243_rook_probe import (
    core_base_pairs,
    core_roundtrip_ok,
    boundary_roundtrip_ok,
    core_orbit_profile,
    boundary_orbit_profile,
    accounting,
)


def test_core_base_is_ternary27():
    assert len(core_base_pairs()) == 27
    assert len(set(core_base_pairs())) == 27
    assert core_roundtrip_ok()


def test_boundary_is_ternary27():
    assert boundary_roundtrip_ok()


def test_action_profiles():
    assert core_orbit_profile() == {3: 27, 6: 27}
    assert boundary_orbit_profile() == {3: 3, 6: 3}


def test_accounting():
    assert accounting() == {
        "phase_pairs": 630,
        "same_plane": 36,
        "rook": 270,
        "nonrook": 324,
        "core": 243,
        "axis_boundary": 27,
    }


if __name__ == "__main__":
    test_core_base_is_ternary27()
    test_boundary_is_ternary27()
    test_action_profiles()
    test_accounting()
    print("ok")
