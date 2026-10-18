from dashi_repo_history.agda import build_semantic_graph, extract_file


def test_where_helper_has_explicit_local_ownership_edge():
    extraction = extract_file(
        "Mini.agda",
        b"""
module Mini where
open import Agda.Builtin.Nat using (Nat)

f : Nat -> Nat
f x = x
  where
    helper : Nat -> Nat
    helper y = y
""",
    )
    graph = build_semantic_graph([extraction])

    f = next(
        node for node in graph.nodes.values()
        if node.kind == "function"
        and node.label == "f"
        and node.scope is None
    )
    helper = next(
        node for node in graph.nodes.values()
        if node.kind == "function"
        and node.label == "helper"
        and node.scope is not None
    )

    assert any(
        edge.source == helper.symbol_id
        and edge.target == f.symbol_id
        and edge.kind == "local-to"
        for edge in graph.edges.values()
    )
