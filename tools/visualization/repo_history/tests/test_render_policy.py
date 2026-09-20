from dashi_repo_history.render_policy import EdgePolicy


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
