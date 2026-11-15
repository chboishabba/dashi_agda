from __future__ import annotations

from agda_preflight.ao_fleet_dynamic_048de098571f import (
    MACROSCOPIC_EIGEN_MOTIF,
    NO_TYPED_MEET,
    SAME_SHARD,
    canonical_leaf_ref_map,
    canonical_leaf_shards,
    emit_logical_shard_refs,
    pairwise_typed_relation,
)


EXPECTED_REFS = {
    "actor": "ipfs://bafkreigrjx2v3oawzjjrhxvcfmqq3tmvnzlxaoxkklrbem2gonb73krimu",
    "temporal": "ipfs://bafkreic2gzg2axzs6icmvqfavdh5mqrm3lmardh4jyq5wnuzuvnzq6mhc4",
    "patient": "ipfs://bafkreies34fpswwuvzxe5b3xge3kmcnf4wum7mlwbqgct2zubiuvbscerm",
    "macroscopic-eigen-motif": "ipfs://bafkreihoh4e2psjzzt6efhmg7bd3uz3ovnejyrprgkdzaewzxsqphlfwiq",
}


def test_canonical_leaf_emits_exact_deterministic_ipfs_refs() -> None:
    assert canonical_leaf_ref_map() == EXPECTED_REFS


def test_macroscopic_eigen_motif_is_exact() -> None:
    assert MACROSCOPIC_EIGEN_MOTIF == (
        "actor:parsed:NominalSubject · "
        "temporal:now:TemporalModifier · "
        "patient:collapse:DirectObject"
    )


def test_logical_shard_emission_is_input_order_independent() -> None:
    shards = canonical_leaf_shards()
    reverse_order = dict(reversed(tuple(shards.items())))

    forward = {item.shard_id: item.uri for item in emit_logical_shard_refs(shards)}
    reverse = {
        item.shard_id: item.uri
        for item in emit_logical_shard_refs(reverse_order)
    }

    assert forward == reverse == EXPECTED_REFS


def test_changing_one_shard_does_not_change_other_refs() -> None:
    shards = canonical_leaf_shards()
    changed = canonical_leaf_shards()
    changed["actor"] = {
        "slot": "actor",
        "value": "changed",
        "role": "NominalSubject",
    }

    before = {item.shard_id: item.uri for item in emit_logical_shard_refs(shards)}
    after = {item.shard_id: item.uri for item in emit_logical_shard_refs(changed)}

    assert before["actor"] != after["actor"]
    for shard_id in ("temporal", "patient", "macroscopic-eigen-motif"):
        assert before[shard_id] == after[shard_id]


def test_distinct_logical_shards_have_pairwise_no_typed_meet() -> None:
    shard_ids = tuple(canonical_leaf_shards())

    for left in shard_ids:
        assert pairwise_typed_relation(left, left) == SAME_SHARD
        for right in shard_ids:
            if left != right:
                assert pairwise_typed_relation(left, right) == NO_TYPED_MEET


def test_all_canonical_refs_use_ipfs_scheme() -> None:
    assert all(uri.startswith("ipfs://") for uri in canonical_leaf_ref_map().values())
