from phase243_orbit_quotient import (
    all_core_states,
    orbit_profile,
    quotient_tag,
    representative,
)


def test_phase243_orbit_quotient():
    states = all_core_states()
    assert len(states) == 243
    assert orbit_profile() == {3: 27, 6: 27}

    quotient = {quotient_tag(state) for state in states}
    assert len(quotient) == 54

    for tag in quotient:
        assert quotient_tag(representative(tag)) == tag


if __name__ == "__main__":
    test_phase243_orbit_quotient()
    print("ok")
