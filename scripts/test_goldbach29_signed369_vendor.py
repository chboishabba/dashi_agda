from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

PIN = ROOT / "vendor" / "meta-introspector-aok-goldbach29.VENDOR"
BRIDGE = ROOT / "DASHI" / "ComputerScience" / "Goldbach29Signed369VendorBridgeExact.agda"


def test_vendor_pin_and_attribution():
    text = PIN.read_text()
    assert "meta-introspector/aok" in text
    assert "c168223e96f7acc6179044f2a365a92db2e350c3" in text
    assert "AGPL-3.0" in text
    assert "Goldbach29" in text
    assert "Mike Dupont" in text or "meta-introspector" in text


def test_bridge_reuses_signed369_and_descent_owners():
    text = BRIDGE.read_text()
    assert "SignedSSPFRACTRANWeaveExact" in text
    assert "FibreMachineFoundation369Exact" in text
    assert "ConsumerDescentMinimalObserverExact" in text
    assert "externalGoldbach29FractionCount" in text
    assert "externalGoldbach30FractionCount" in text
    assert "fineStateNeedNotEqualCoarseObserver" in text
    assert "goldbachReductionConsumerBoundary" in text


def test_no_unpaid_full_bisimulation_claim():
    text = BRIDGE.read_text()
    assert "fullReachableWeakBisimulationPaid" in text
    assert "fullReachableWeakBisimulationPaid = false" in text
    assert "mikeOwnsGoldbach29Construction" in text
    assert "dashiOwnsObserverTranslation" in text
