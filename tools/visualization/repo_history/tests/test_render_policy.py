from dashi_repo_history.render_policy import EdgePolicy, LabelPolicy


def test_edge_policy_prioritizes_construction_over_weaker_relations():
    policy = EdgePolicy()
    kinds = {"contains", "body-depends", "constructs"}
    assert policy.dominant_kind(kinds) == "constructs"
    assert policy.stroke_width(kinds) == 4.0


def test_call_style_is_stronger_than_type_dependency():
    policy = EdgePolicy()
    assert policy.stroke_width({"calls"}) > policy.stroke_width({"type-depends"})


def test_projection_style_is_deterministic_under_set_order():
    policy = EdgePolicy()
    left = policy.edge_config({"calls", "contains"})
    right = policy.edge_config({"contains", "calls"})
    assert left == right


def test_long_semantic_labels_are_compacted_without_losing_both_ends():
    policy = LabelPolicy(max_label_chars=24)
    node = {
        "label": "canonicalProofGrowthAnimationExact",
        "kind": "function",
    }

    label = policy.compact_label(node)

    assert len(label) <= 25
    assert label.startswith("canonical")
    assert label.endswith("tionExact")
    assert "…" in label


def test_module_label_uses_leaf_name_before_compaction():
    policy = LabelPolicy(max_label_chars=40)
    node = {
        "label": "DASHI.Visual.ProofGrowthAnimationExact",
        "kind": "module",
    }

    assert policy.compact_label(node) == "ProofGrowthAnimationExact"
