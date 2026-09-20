from dashi_repo_history.agda import build_semantic_graph, extract_file


SOURCE = b"""
module Mini where

open import Agda.Builtin.Nat using (Nat)

idNat : (x : Nat) -> Nat
idNat x = x

use : (x : Nat) -> Nat
use x = idNat x
"""


def test_tree_sitter_extracts_functions_binders_and_dependencies():
    extraction = extract_file("Mini.agda", SOURCE)
    graph = build_semantic_graph([extraction])

    labels = {(node.label, node.kind) for node in graph.nodes.values()}
    assert ("Mini", "module") in labels
    assert ("idNat", "function") in labels
    assert ("use", "function") in labels
    assert any(label == "x" and kind == "binder" for label, kind in labels)

    by_label = {
        node.label: node
        for node in graph.nodes.values()
        if node.kind != "binder"
    }
    id_nat = by_label["idNat"]
    use = by_label["use"]

    assert any(
        edge.source == id_nat.symbol_id
        and edge.target == use.symbol_id
        and edge.kind == "body-depends"
        for edge in graph.edges.values()
    )
    assert any(edge.kind == "binds" for edge in graph.edges.values())


def test_multi_binder_produces_two_scoped_variables_not_the_type():
    extraction = extract_file(
        "Mini.agda",
        b"""
module Mini where
open import Agda.Builtin.Nat using (Nat)
pairish : (x y : Nat) -> Nat
pairish x y = x
""",
    )
    graph = build_semantic_graph([extraction])
    binders = [
        node.label
        for node in graph.nodes.values()
        if node.kind == "binder"
    ]
    assert "x" in binders
    assert "y" in binders
    assert "Nat" not in binders
