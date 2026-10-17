import math

from dynamic_detrapping_probe import (
    control_frequency_lower_bound,
    adiabatic_control_frequency_upper_bound,
    detrapping_window_exists,
    minimum_triadic_depth_for_turning_time,
    resonance_clear,
)


def test_frequency_window():
    lower = control_frequency_lower_bound(math.pi / 3, 1e-4)
    upper = adiabatic_control_frequency_upper_bound(2e7, 1e-2)
    assert math.isclose(lower, (math.pi / 3) / 1e-4)
    assert math.isclose(upper, 2e5)
    assert detrapping_window_exists(lower, upper)


def test_no_window_when_turning_is_too_fast():
    lower = control_frequency_lower_bound(math.pi, 1e-7)
    upper = adiabatic_control_frequency_upper_bound(2e7, 1e-2)
    assert not detrapping_window_exists(lower, upper)


def test_triadic_depth_from_phase_update_time():
    assert minimum_triadic_depth_for_turning_time(2e5, 1e-4) == 1
    assert minimum_triadic_depth_for_turning_time(2e4, 1e-5) >= 4


def test_resonance_clearance():
    assert resonance_clear(2e5, [5e4, 2e7], relative_margin=0.05, max_harmonic=3)
    assert not resonance_clear(1e5, [5e4], relative_margin=0.05, max_harmonic=3)


if __name__ == "__main__":
    test_frequency_window()
    test_no_window_when_turning_is_too_fast()
    test_triadic_depth_from_phase_update_time()
    test_resonance_clearance()
    print("ok")
