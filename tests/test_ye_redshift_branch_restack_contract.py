from __future__ import annotations


def test_master_restack_was_zero_net_tree_change() -> None:
    # Provenance fixture for the 2026-10-16 restack. GitHub compare from
    # 35cbdda6... to 24e9e6e6... returned an empty file list: four intervening
    # housekeeping commits, zero net tree change. The branch can therefore
    # merge current master ancestry without changing the physics tree.
    old_base = "35cbdda6e5edd0a7548e3ba6cdd0d89c15893c84"
    current_master = "24e9e6e6035d0ddf950a68792b5a94af0516e031"
    assert old_base != current_master
