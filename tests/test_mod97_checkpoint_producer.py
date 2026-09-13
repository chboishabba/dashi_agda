from scripts.mod97_checkpoint_producer import (
    Mod97RunConfig,
    build_manifest,
    checkpoint_epochs,
    deterministic_split_indices,
)


def test_checkpoint_schedule_includes_zero_and_horizon() -> None:
    assert checkpoint_epochs(15000, 1000) == list(range(0, 15001, 1000))


def test_checkpoint_schedule_keeps_nondivisible_horizon() -> None:
    assert checkpoint_epochs(105, 20) == [0, 20, 40, 60, 80, 100, 105]


def test_split_is_deterministic_and_has_exact_historical_geometry() -> None:
    train_a, test_a = deterministic_split_indices(9409, 2822, 17)
    train_b, test_b = deterministic_split_indices(9409, 2822, 17)
    train_c, _ = deterministic_split_indices(9409, 2822, 18)

    assert train_a == train_b
    assert test_a == test_b
    assert len(train_a) == 2822
    assert len(test_a) == 6587
    assert set(train_a).isdisjoint(test_a)
    assert sorted(train_a + test_a) == list(range(9409))
    assert train_a != train_c


def test_manifest_refuses_historical_identity_promotion() -> None:
    config = Mod97RunConfig(
        seed=0,
        split_seed=17,
        weight_decay_milli=600,
        embedding_dim=32,
        hidden_dim=128,
        checkpoint_cadence=1000,
    )
    manifest = build_manifest(config)

    assert manifest["task"]["modulus"] == 97
    assert manifest["task"]["total_pairs"] == 9409
    assert manifest["task"]["training_pairs"] == 2822
    assert manifest["task"]["test_pairs"] == 6587
    assert manifest["training"]["optimizer"] == "AdamW"
    assert manifest["training"]["learning_rate"] == 0.001
    assert manifest["training"]["horizon"] == 15000
    assert manifest["training"]["measurement_cadence"] == 20
    assert manifest["architecture"]["shared_residue_embedding"] is True
    assert manifest["architecture"]["activation"] == "ReLU"
    assert manifest["architecture"]["output_classes"] == 97
    assert manifest["provenance"]["historical_receipt_same_run"] is False
    assert manifest["provenance"]["historical_receipt_same_configuration"] is False
    assert manifest["provenance"]["historical_checkpoint_reconstruction"] is False
    assert "embedding/hidden widths" in manifest["provenance"]["historical_gap"]
    assert "split-generation procedure" in manifest["provenance"]["historical_gap"]


def test_invalid_dimensions_fail_closed() -> None:
    try:
        Mod97RunConfig(
            seed=0,
            split_seed=17,
            weight_decay_milli=600,
            embedding_dim=0,
            hidden_dim=128,
            checkpoint_cadence=1000,
        )
    except ValueError as exc:
        assert "embedding_dim" in str(exc)
    else:
        raise AssertionError("zero embedding_dim must fail closed")
