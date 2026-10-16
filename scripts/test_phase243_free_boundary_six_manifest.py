from phase243_free_boundary_six_manifest import AALI, AOFF, XOFF, shortlist, validate


def test_manifest_structure():
    receipt = validate()
    assert receipt["candidate_count"] == 6
    assert receipt["geometry_phase_identity_count"] == 3
    assert receipt["abc_allocation_count_per_identity"] == 2
    assert receipt["all_coil_proxy_residuals_below_baseline"] is True


def test_each_geometry_has_two_abc_allocations():
    xs = shortlist()
    for tag in (AOFF, AALI, XOFF):
        rows = [x for x in xs if x.tag == tag]
        assert {x.delta_c for x in rows} == {0.75, 1.0}
        assert all(abs(x.mach * x.mach + x.alpha + x.delta_c - 1.0) < 1e-12 for x in rows)


if __name__ == "__main__":
    test_manifest_structure()
    test_each_geometry_has_two_abc_allocations()
    print("PASS")
