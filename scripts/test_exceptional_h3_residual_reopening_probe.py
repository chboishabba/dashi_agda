from exceptional_h3_residual_reopening_probe import verify


def test_exceptional_h3_residual_reopening_probe():
    receipt = verify()
    assert receipt["carrier_states"] == 27
    assert receipt["phase_kernel_states"] == 9
    assert receipt["phase_values"] == 3
    assert receipt["quadratic_constant_on_all_radical_cosets"] is True
    assert receipt["split_reopen_roundtrip_all_states"] is True
    assert receipt["kernel_times_phase_pairs"] == 27
    assert receipt["phase_is_exact_reopening_residual"] is True
    assert receipt["phase_is_three_h3_patch_fibre"] is False
