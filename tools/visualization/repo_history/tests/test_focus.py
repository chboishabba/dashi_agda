import pytest

from dashi_repo_history.focus import focus_symbol, resolve_symbol


def _graph():
    return {
        "nodes": [
            {"symbol_id": "x", "label": "x", "module": "M", "kind": "binder"},
            {"symbol_id": "g", "label": "g", "module": "M", "kind": "function"},
            {"symbol_id": "f", "label": "f", "module": "M", "kind": "function"},
            {"symbol_id": "h", "label": "h", "module": "M", "kind": "function"},
        ],
        "edges": [
            {
                "relation_id": "x-g",
                "source": "x",
                "target": "g",
                "kind": "argument-to",
            },
            {
                "relation_id": "g-f",
                "source": "g",
                "target": "f",
                "kind": "calls",
            },
            {
                "relation_id": "f-h",
                "source": "f",
                "target": "h",
                "kind": "calls",
            },
        ],
    }


def test_focus_walks_dependencies_upstream_and_consumers_downstream():
    result = focus_symbol(
        _graph(),
        "f",
        upstream_depth=2,
        downstream_depth=1,
    )
    assert result.root_id == "f"
    assert result.node_ids == frozenset({"x", "g", "f", "h"})
    assert result.edge_ids == frozenset({"x-g", "g-f", "f-h"})


def test_focus_depth_limits_dependency_expansion():
    result = focus_symbol(
        _graph(),
        "f",
        upstream_depth=1,
        downstream_depth=0,
    )
    assert result.node_ids == frozenset({"g", "f"})
    assert result.edge_ids == frozenset({"g-f"})


def test_resolve_symbol_rejects_ambiguous_labels():
    graph = _graph()
    graph["nodes"].append(
        {
            "symbol_id": "other-f",
            "label": "f",
            "module": "Other",
            "kind": "function",
        }
    )
    with pytest.raises(ValueError):
        resolve_symbol(graph, "f")


def test_focus_layers_reveal_root_then_nearest_upstream_then_downstream():
    result = focus_symbol(
        _graph(),
        "f",
        upstream_depth=2,
        downstream_depth=1,
    )
    assert result.layers[0] == ("f",)
    assert result.layers[1] == ("g",)
    assert result.layers[2] == ("x",)
    assert result.layers[3] == ("h",)


def test_module_qualified_selector_disambiguates_label():
    graph = _graph()
    graph["nodes"].append(
        {
            "symbol_id": "other-f",
            "label": "f",
            "module": "Other",
            "kind": "function",
        }
    )
    resolved = resolve_symbol(graph, "M::f")
    assert resolved["symbol_id"] == "f"
