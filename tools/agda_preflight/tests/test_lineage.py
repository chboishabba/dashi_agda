from agda_preflight.lineage import compute_round_lineage


def test_lineage_orders_rounds_and_reports_novelty():
    modules = [
        {
            "module_name": "DASHI.Physics.Closure.FooRound1Exact",
            "symbols": [
                {"qualified_name": "A", "signature_sha256": "a"},
                {"qualified_name": "B", "signature_sha256": "b"},
            ],
        },
        {
            "module_name": "DASHI.Physics.Closure.FooRound2Exact",
            "symbols": [
                {"qualified_name": "A", "signature_sha256": "a"},
                {"qualified_name": "B", "signature_sha256": "b2"},
                {"qualified_name": "C", "signature_sha256": "c"},
            ],
        },
    ]

    report = compute_round_lineage(modules)
    family = report["families"][0]
    transition = family["transitions"][0]
    assert family["rounds"] == [1, 2]
    assert transition["added"] == 1
    assert transition["removed"] == 0
    assert transition["signature_changed"] == 1
    assert transition["unchanged"] == 1
    assert transition["novelty_ratio"] == 2 / 3
    assert transition["snapshot_noise_ratio"] == 1 / 3


def test_lineage_ignores_non_round_modules():
    report = compute_round_lineage([
        {"module_name": "DASHI.Core.Foo", "symbols": []},
    ])
    assert report == {"families": []}
