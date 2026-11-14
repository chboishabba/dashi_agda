from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def text(path: str) -> str:
    return (ROOT / path).read_text(encoding="utf-8")


def test_brainit_connectome_weld_exists_and_reuses_repo_spine():
    p = "DASHI/Biology/BrainITConnectomeFMRIWeldExact.agda"
    s = text(p)
    assert "BrainConnectomeFMRIObservationQuotient" in s
    assert "BidirectionalBrainObservationQuotient" in s
    assert "FunctionalConnectomeBodyMemoryBridge" in s
    assert "BrainITFunctionalClusterTransferExact" in s


def test_brainit_clusters_do_not_collapse_to_structural_connectome():
    s = text("DASHI/Biology/BrainITConnectomeFMRIWeldExact.agda")
    assert "functionalClustersAreStructuralConnectomeEdgesIsFalse" in s
    assert "sharedClustersRecoverLatentBrainStateIsFalse" in s
    assert "brainITReadoutRemainsLossyObservationIsTrue" in s


def test_brainit_weld_is_exported():
    s = text("DASHI/Biology/Everything.agda")
    assert "import DASHI.Biology.BrainITConnectomeFMRIWeldExact" in s
