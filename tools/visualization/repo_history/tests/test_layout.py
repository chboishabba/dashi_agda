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


def test_large_graph_bypasses_spring_layout(monkeypatch):
    from dashi_repo_history.layout import LayoutConfig, PersistentLayout

    called = False

    def fail_if_called(*args, **kwargs):
        nonlocal called
        called = True
        raise AssertionError("spring_layout should not run for large graph")

    monkeypatch.setattr("dashi_repo_history.layout.nx.spring_layout", fail_if_called)

    layout = PersistentLayout(
        LayoutConfig(
            spring_node_limit=10,
            spring_edge_limit=20,
        )
    )
    nodes = [f"n{i}" for i in range(30)]
    edges = [(f"n{i}", f"n{i + 1}") for i in range(29)]

    solved = layout.solve(nodes, edges)

    assert called is False
    assert set(solved) == set(nodes)


def test_large_layout_preserves_existing_positions():
    from dashi_repo_history.layout import LayoutConfig, PersistentLayout

    layout = PersistentLayout(
        LayoutConfig(
            spring_node_limit=2,
            spring_edge_limit=2,
        )
    )
    layout.positions = {"a": (0.25, -0.5)}

    solved = layout.solve(
        ["a", "b", "c"],
        [("a", "b"), ("b", "c")],
    )

    assert solved["a"] == (0.25, -0.5)
    assert "b" in solved
    assert "c" in solved
