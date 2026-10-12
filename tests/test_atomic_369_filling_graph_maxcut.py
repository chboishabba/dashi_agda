from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def test_atomic_filling_graph_sources_exist():
    required = [
        ROOT / "DASHI/Physics/Chemistry/AtomicPeriodicTable369FillingGraphExact.agda",
        ROOT / "DASHI/Physics/Chemistry/AtomicPeriodicTable369TernaryRealizationIntertwinerExact.agda",
        ROOT / "scripts/plot_atomic_369_filling_graph.py",
    ]
    for path in required:
        assert path.exists(), path


def test_first_three_period_filling_closures():
    # Exact structural Madelung prefix through Ar:
    # 1s^2 | 2s^2 2p^6 | 3s^2 3p^6
    block_capacities = [2, 2, 6, 2, 6]
    cumulative = []
    total = 0
    for cap in block_capacities:
        total += cap
        cumulative.append(total)
    assert cumulative == [2, 4, 10, 12, 18]
    assert [cumulative[i] for i in (0, 2, 4)] == [2, 10, 18]


def test_realization_firewall_is_explicit():
    text = (ROOT / "DASHI/Physics/Chemistry/AtomicPeriodicTable369TernaryRealizationIntertwinerExact.agda").read_text()
    assert "sameCardinalityConstructsRealization" in text
    assert "false refl" in text
    assert "intertwines" in text
