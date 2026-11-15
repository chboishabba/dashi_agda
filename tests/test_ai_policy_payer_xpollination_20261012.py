from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def require(path: str, markers: list[str]) -> None:
    text = (ROOT / path).read_text(encoding="utf-8")
    for marker in markers:
        assert marker in text, f"missing {marker!r} in {path}"


def test_policy_causal_admission_surface() -> None:
    require(
        "DASHI/Economics/AIPolicyCausalAdmission20261012Exact.agda",
        [
            "australiaObservedPolicySubstratePaid",
            "sameBasisBurdenMeasurementStillOpen",
            "reviewedCausalBridgeStillOpen",
            "observedPolicyFactsDoNotCreateConcentrationCause",
            "intentionalCaptureStillSeparate",
        ],
    )


def test_terminal_payer_consumer_sufficiency_surface() -> None:
    require(
        "DASHI/Economics/AITerminalPayerConsumerSufficiency20261012Exact.agda",
        [
            "selectedMicrosoftCapacityConsumerPaid",
            "selectedMetaCapacityConsumerPaid",
            "selectedOpenAICashConsumerOpen",
            "coreWeaveExhaustiveIndependenceConsumerOpen",
            "selectedPayerCapacityDoesNotCreateExhaustiveIndependence",
            "consumerRelativeTerminalBoundary",
        ],
    )


def test_same_capability_scarcity_admission_surface() -> None:
    require(
        "DASHI/Economics/AISameCapabilityScarcityRentAdmission20261012Exact.agda",
        [
            "selectedPairPriceReceiptPaid",
            "selectedPairCapabilityMatchedIsFalse",
            "matchedScarcityRentAdmissionStillOpen",
            "benchmarkNormalisationDoesNotCreateMatchedPair",
            "scarcityRentAdmissionBoundary",
        ],
    )


def test_rollup_wires_xpollinations() -> None:
    require(
        "DASHI/Economics/AIEntanglementEverything2026.agda",
        [
            "AIPolicyCausalAdmission20261012Exact",
            "AITerminalPayerConsumerSufficiency20261012Exact",
            "AISameCapabilityScarcityRentAdmission20261012Exact",
        ],
    )
