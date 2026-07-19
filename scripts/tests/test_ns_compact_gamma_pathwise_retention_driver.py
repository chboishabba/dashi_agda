from __future__ import annotations

import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent.parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import ns_compact_gamma_pathwise_retention_driver as driver
from ns_compact_gamma_common_u_net_audit import PacketParameters


def call_builder(**overrides):
    parameters = PacketParameters(
        triad_count=4,
        phase_spread=0.5,
        target_ratio=2.5,
        satellite_fraction=0.55,
    )
    arguments = {
        "split": "matched-member",
        "base_parameters": (parameters,),
        "seeds": (12345,),
        "samples_per_base": 1,
        "perturb": False,
        "phase_jitter": 0.0,
        "log_ratio_jitter": 0.0,
        "log_satellite_jitter": 0.0,
        "cutoff": 32,
        "target_shells": (2,),
        "nu": 0.01,
        "input_amplitude": 0.1,
        "target_packet_energy": 0.86,
        "gamma_threshold": 0.5,
        "end_parabolic_time": 0.004,
        "output_count": 3,
        "cfl": 0.2,
    }
    arguments.update(overrides)
    return driver.build_split_profiles_with_exact_matched_seed(**arguments)


def test_matched_builder_preserves_source_seed(monkeypatch) -> None:
    observed = {}

    def fake_build_profile(**kwargs):
        observed.update(kwargs)
        return {
            "profile_id": "matched",
            "parameters": {
                "triad_count": kwargs["parameters"].triad_count,
                "phase_spread": kwargs["parameters"].phase_spread,
                "target_ratio": kwargs["parameters"].target_ratio,
                "satellite_fraction": kwargs["parameters"].satellite_fraction,
            },
        }

    monkeypatch.setattr(driver, "build_profile", fake_build_profile)
    profiles = call_builder()
    assert observed["seed"] == 12345
    assert profiles[0]["derived_state_seed"] == 12345
    assert profiles[0]["perturbation_sample_index"] == 0


def test_nonmatched_split_delegates_unchanged(monkeypatch) -> None:
    sentinel = [{"profile_id": "delegated"}]
    observed = {}

    def fake_original(**kwargs):
        observed.update(kwargs)
        return sentinel

    monkeypatch.setattr(driver, "_original_build_split_profiles", fake_original)
    result = call_builder(split="holdout")
    assert result is sentinel
    assert observed["seeds"] == (12345,)
    assert observed["split"] == "holdout"


def test_matched_builder_rejects_jitter() -> None:
    try:
        call_builder(phase_jitter=0.1)
    except ValueError as error:
        assert "zero jitter" in str(error)
    else:
        raise AssertionError("matched-cutoff reconstruction accepted jitter")
