from dashi_repo_history.layout import LayoutConfig, PersistentLayout


def test_persistent_layout_preserves_existing_node_identity_and_near_position():
    layout = PersistentLayout(
        LayoutConfig(iterations=20, old_position_weight=0.95)
    )
    first = layout.solve(["a", "b"], [("a", "b")])
    second = layout.solve(["a", "b", "c"], [("a", "b"), ("b", "c")])

    assert set(second) == {"a", "b", "c"}
    for node in ("a", "b"):
        dx = abs(second[node][0] - first[node][0])
        dy = abs(second[node][1] - first[node][1])
        assert dx < 0.5
        assert dy < 0.5
