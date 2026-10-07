from __future__ import annotations

import importlib.util
import math
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]


def read(rel: str) -> str:
    path = REPO_ROOT / rel
    assert path.is_file(), f"missing {rel}"
    return path.read_text(encoding="utf-8", errors="replace")


def load_benchmark_module():
    path = REPO_ROOT / "scripts" / "schutzhold_emgw_benchmark.py"
    spec = importlib.util.spec_from_file_location("schutzhold_emgw_benchmark", path)
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_em_energy_loss_maps_to_negative_frequency_shift() -> None:
    text = read("DASHI/Physics/GR/ControlledEMGWReadoutSignPropagationExact.agda")
    assert "frequencySignFromWorkSign sign = flipReadoutSign sign" in text
    assert "emissionFrequencySignIsNegative" in text
    assert "absorptionFrequencySignIsPositive" in text


def test_same_object_welds_use_propositional_equality() -> None:
    weld = read("DASHI/Physics/YangMills/MaxwellHodgeR144ControlledExchangeWeldExact.agda")
    assert "interactionFromMaxwellHodge" in weld
    assert "interactionFromR144" in weld
    assert "sameInteraction : interactionFromMaxwellHodge" in weld
    assert "≡ interactionFromR144" in weld
    assert "SameInteractionReceipt : Set" not in weld

    r144 = read("DASHI/Physics/YangMills/R144EMGWControlledExchangeInstantiationExact.agda")
    assert "controlledExchangeIsWeldInteraction" in r144
    assert "controlledExchange ≡ R144EMGWStressVariationWeld.interaction weld" in r144
    assert "SameControlledInteractionReceipt : Set" not in r144

    anti = read("DASHI/Physics/ExoticGravity/AntigravityControlledGWExchangeCrossPollinationExact.agda")
    assert "ordinaryUsesInteraction" in anti
    assert "alternativeUsesInteraction" in anti
    assert "observationUsesInteraction" in anti
    assert "AttributedExchangePrediction.interaction ordinary ≡ interaction" in anti
    assert "AttributedExchangePrediction.interaction alternative ≡ interaction" in anti
    assert "ControlledExchangeObservation.interaction observed ≡ interaction" in anti

    compiler = read("DASHI/Physics/ExoticGravity/AntigravityControlledGWExchangeMaxCutCompilerExact.agda")
    assert "maxwellAndR144InteractionsEqual" in compiler
    assert "ordinaryUsesPhysicalInteraction" in compiler
    assert "alternativeUsesPhysicalInteraction" in compiler
    assert "observationUsesPhysicalInteraction" in compiler
    assert "ordinaryUsesPhysicalInteraction : Set" not in compiler

    terminal = read("DASHI/Physics/ExoticGravity/SchutzholdAntigravityTerminalMaxCutExact.agda")
    assert "ordinaryUsesPhysicalInteraction" in terminal
    assert "alternativeUsesPhysicalInteraction" in terminal
    assert "observationUsesPhysicalInteraction" in terminal
    assert "OrdinaryUsesPhysicalInteractionReceipt : Set" not in terminal


def test_zero_strain_returns_infinite_required_delay() -> None:
    mod = load_benchmark_module()
    result = mod.evaluate(mod.Benchmark(strain=0.0))
    assert result["differential_delta_omega_s^-1"] == 0.0
    assert result["relative_phase_rad"] == 0.0
    assert math.isinf(result["minimum_delay_for_target_snr_s"])
    assert math.isinf(result["minimum_path_for_target_snr_m"])


def test_custom_reflection_count_verify_uses_parameterized_loss_budget() -> None:
    mod = load_benchmark_module()
    b = mod.Benchmark(reflection_count=500_000)
    result = mod.verify(b)
    expected_half = 1.0 - math.exp(math.log(0.5) / b.reflection_count)
    expected_tenth = 1.0 - math.exp(math.log(0.1) / b.reflection_count)
    assert math.isclose(result["loss_per_reflection_for_50pct_survival"], expected_half)
    assert math.isclose(result["loss_per_reflection_for_10pct_survival"], expected_tenth)
