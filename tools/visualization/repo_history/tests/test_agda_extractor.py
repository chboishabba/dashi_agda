from copy import deepcopy
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
        and edge.kind in {"body-depends", "calls"}
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


def test_bare_function_pattern_becomes_clause_scoped_binder():
    extraction = extract_file(
        "Mini.agda",
        b"""
module Mini where
open import Agda.Builtin.Nat using (Nat)
idNat : Nat -> Nat
idNat x = x
""",
    )
    graph = build_semantic_graph([extraction])

    functions = [
        node for node in graph.nodes.values()
        if node.kind == "function" and node.label == "idNat"
    ]
    assert len(functions) == 1
    owner = functions[0]

    binders = [
        node for node in graph.nodes.values()
        if node.kind == "binder" and node.label == "x"
    ]
    assert len(binders) == 1
    binder = binders[0]

    assert any(
        edge.source == binder.symbol_id
        and edge.target == owner.symbol_id
        and edge.kind == "binds"
        for edge in graph.edges.values()
    )
    assert any(
        edge.source == binder.symbol_id
        and edge.target == owner.symbol_id
        and edge.kind in {"body-depends", "value-flows"}
        for edge in graph.edges.values()
    )
    assert not any(
        unresolved["reference"] == "x"
        for unresolved in graph.unresolved_references
    )


def test_data_constructor_patterns_are_not_promoted_to_binders():
    extraction = extract_file(
        "Mini.agda",
        b"""
module Mini where

data Bit : Set where
  zero : Bit
  one : Bit

flip : Bit -> Bit
flip zero = one
flip one = zero
""",
    )
    graph = build_semantic_graph([extraction])

    by_label = {}
    for node in graph.nodes.values():
        by_label.setdefault(node.label, []).append(node)

    constructors = {
        node.label: node
        for label in ("zero", "one")
        for node in by_label.get(label, [])
        if node.kind == "constructor"
    }
    assert set(constructors) == {"zero", "one"}

    functions = [
        node for node in by_label.get("flip", [])
        if node.kind == "function"
    ]
    assert len(functions) == 1
    flip = functions[0]

    assert not any(
        node.kind == "binder" and node.label in {"zero", "one"}
        for node in graph.nodes.values()
    )

    matched = {
        edge.source
        for edge in graph.edges.values()
        if edge.target == flip.symbol_id
        and edge.kind == "pattern-matches"
    }
    assert matched == {
        constructors["zero"].symbol_id,
        constructors["one"].symbol_id,
    }


def test_same_pattern_spelling_in_different_clauses_has_distinct_scope():
    extraction = extract_file(
        "Mini.agda",
        b"""
module Mini where

data Maybe : Set where
  none : Maybe
  some : Maybe -> Maybe

pick : Maybe -> Maybe
pick none = none
pick (some x) = x

other : Maybe -> Maybe
other (some x) = x
other none = none
""",
    )
    graph = build_semantic_graph([extraction])

    xs = [
        node for node in graph.nodes.values()
        if node.kind == "binder" and node.label == "x"
    ]
    assert len(xs) == 2
    assert xs[0].symbol_id != xs[1].symbol_id
    assert xs[0].scope != xs[1].scope


def test_record_fields_and_constructor_have_container_relations():
    extraction = extract_file(
        "Mini.agda",
        b"""
module Mini where
open import Agda.Builtin.Nat using (Nat)

record Pair : Set where
  constructor mkPair
  field
    left : Nat
    right : Nat
""",
    )
    graph = build_semantic_graph([extraction])

    nodes = list(graph.nodes.values())
    pair = next(
        node for node in nodes
        if node.kind == "record" and node.label == "Pair"
    )
    constructor = next(
        node for node in nodes
        if node.kind == "constructor" and node.label == "mkPair"
    )
    fields = {
        node.label: node
        for node in nodes
        if node.kind == "field" and node.label in {"left", "right"}
    }
    assert set(fields) == {"left", "right"}

    assert any(
        edge.source == constructor.symbol_id
        and edge.target == pair.symbol_id
        and edge.kind == "constructor-of"
        for edge in graph.edges.values()
    )
    for field in fields.values():
        assert any(
            edge.source == field.symbol_id
            and edge.target == pair.symbol_id
            and edge.kind == "field-of"
            for edge in graph.edges.values()
        )


def test_open_import_admits_unqualified_dependency():
    a = extract_file(
        "A.agda",
        b"""
module A where
foo : Set
foo = Set
""",
    )
    b = extract_file(
        "B.agda",
        b"""
module B where
open import A
bar : Set
bar = foo
""",
    )
    graph = build_semantic_graph([a, b])

    foo = next(
        node for node in graph.nodes.values()
        if node.module == "A" and node.label == "foo"
    )
    bar = next(
        node for node in graph.nodes.values()
        if node.module == "B" and node.label == "bar"
    )
    assert any(
        edge.source == foo.symbol_id
        and edge.target == bar.symbol_id
        and edge.kind == "body-depends"
        for edge in graph.edges.values()
    )


def test_plain_import_does_not_admit_unqualified_unique_name():
    a = extract_file(
        "A.agda",
        b"""
module A where
foo : Set
foo = Set
""",
    )
    b = extract_file(
        "B.agda",
        b"""
module B where
import A
bar : Set
bar = foo
""",
    )
    graph = build_semantic_graph([a, b])

    bar = next(
        node for node in graph.nodes.values()
        if node.module == "B" and node.label == "bar"
    )
    assert any(
        unresolved["owner"] == bar.symbol_id
        and unresolved["reference"] == "foo"
        for unresolved in graph.unresolved_references
    )


def test_plain_import_allows_qualified_dependency():
    a = extract_file(
        "A.agda",
        b"""
module A where
foo : Set
foo = Set
""",
    )
    b = extract_file(
        "B.agda",
        b"""
module B where
import A
bar : Set
bar = A.foo
""",
    )
    graph = build_semantic_graph([a, b])

    foo = next(
        node for node in graph.nodes.values()
        if node.module == "A" and node.label == "foo"
    )
    bar = next(
        node for node in graph.nodes.values()
        if node.module == "B" and node.label == "bar"
    )
    assert any(
        edge.source == foo.symbol_id
        and edge.target == bar.symbol_id
        for edge in graph.edges.values()
    )


def test_open_import_using_does_not_admit_other_unique_names():
    a = extract_file(
        "A.agda",
        b"""
module A where
foo : Set
foo = Set
baz : Set
baz = Set
""",
    )
    b = extract_file(
        "B.agda",
        b"""
module B where
open import A using (foo)
bar : Set
bar = foo
quux : Set
quux = baz
""",
    )
    graph = build_semantic_graph([a, b])

    bar = next(
        node for node in graph.nodes.values()
        if node.module == "B" and node.label == "bar"
    )
    quux = next(
        node for node in graph.nodes.values()
        if node.module == "B" and node.label == "quux"
    )
    assert not any(
        unresolved["owner"] == bar.symbol_id
        and unresolved["reference"] == "foo"
        for unresolved in graph.unresolved_references
    )
    assert any(
        unresolved["owner"] == quux.symbol_id
        and unresolved["reference"] == "baz"
        for unresolved in graph.unresolved_references
    )


def test_open_import_renaming_resolves_visible_alias_only():
    a = extract_file(
        "A.agda",
        b"""
module A where
foo : Set
foo = Set
""",
    )
    b = extract_file(
        "B.agda",
        b"""
module B where
open import A renaming (foo to qux)
bar : Set
bar = qux
bad : Set
bad = foo
""",
    )
    graph = build_semantic_graph([a, b])

    foo = next(
        node for node in graph.nodes.values()
        if node.module == "A" and node.label == "foo"
    )
    bar = next(
        node for node in graph.nodes.values()
        if node.module == "B" and node.label == "bar"
    )
    bad = next(
        node for node in graph.nodes.values()
        if node.module == "B" and node.label == "bad"
    )

    assert any(
        edge.source == foo.symbol_id
        and edge.target == bar.symbol_id
        for edge in graph.edges.values()
    )
    assert any(
        unresolved["owner"] == bad.symbol_id
        and unresolved["reference"] == "foo"
        for unresolved in graph.unresolved_references
    )


def test_signature_and_definition_references_have_distinct_edge_kinds():
    extraction = extract_file(
        "Mini.agda",
        b"""
module Mini where
open import Agda.Builtin.Nat using (Nat)
base : Nat
base = 0
use : Nat
use = base
""",
    )
    builtin_nat = extract_file(
        "Agda/Builtin/Nat.agda",
        b"""
module Agda.Builtin.Nat where
postulate
  Nat : Set
""",
    )
    graph = build_semantic_graph([builtin_nat, extraction])

    nat_edges = [
        edge
        for edge in graph.edges.values()
        if edge.kind == "type-depends"
    ]
    body_edges = [
        edge
        for edge in graph.edges.values()
        if edge.kind == "body-depends"
    ]

    use = next(
        node for node in graph.nodes.values()
        if node.label == "use" and node.kind == "function"
    )
    base = next(
        node for node in graph.nodes.values()
        if node.label == "base" and node.kind == "function"
    )

    assert nat_edges
    assert any(
        edge.source == base.symbol_id
        and edge.target == use.symbol_id
        for edge in body_edges
    )


def test_open_import_emits_import_and_open_module_relations():
    a = extract_file(
        "A.agda",
        b"""
module A where
foo : Set
foo = Set
""",
    )
    b = extract_file(
        "B.agda",
        b"""
module B where
open import A
bar : Set
bar = foo
""",
    )
    graph = build_semantic_graph([a, b])

    module_a = next(
        node for node in graph.nodes.values()
        if node.kind == "module" and node.label == "A"
    )
    module_b = next(
        node for node in graph.nodes.values()
        if node.kind == "module" and node.label == "B"
    )
    kinds = {
        edge.kind
        for edge in graph.edges.values()
        if edge.source == module_a.symbol_id
        and edge.target == module_b.symbol_id
    }
    assert "imports" in kinds
    assert "opens" in kinds


def test_prefix_application_promotes_function_reference_to_calls():
    extraction = extract_file(
        "Mini.agda",
        b"""
module Mini where
open import Agda.Builtin.Nat using (Nat)

g : Nat -> Nat
g x = x

f : Nat -> Nat
f x = g x
""",
    )
    graph = build_semantic_graph([extraction])
    g = next(
        node for node in graph.nodes.values()
        if node.kind == "function" and node.label == "g"
    )
    f = next(
        node for node in graph.nodes.values()
        if node.kind == "function" and node.label == "f"
    )
    assert any(
        edge.source == g.symbol_id
        and edge.target == f.symbol_id
        and edge.kind == "calls"
        for edge in graph.edges.values()
    )


def test_bare_function_value_stays_body_dependency_not_call():
    extraction = extract_file(
        "Mini.agda",
        b"""
module Mini where
open import Agda.Builtin.Nat using (Nat)

g : Nat -> Nat
g x = x

use : (Nat -> Nat)
use = g
""",
    )
    graph = build_semantic_graph([extraction])
    g = next(
        node for node in graph.nodes.values()
        if node.kind == "function" and node.label == "g"
    )
    use = next(
        node for node in graph.nodes.values()
        if node.kind == "function" and node.label == "use"
    )
    assert any(
        edge.source == g.symbol_id
        and edge.target == use.symbol_id
        and edge.kind == "body-depends"
        for edge in graph.edges.values()
    )
    assert not any(
        edge.source == g.symbol_id
        and edge.target == use.symbol_id
        and edge.kind == "calls"
        for edge in graph.edges.values()
    )


def test_constructor_use_promotes_to_constructs():
    extraction = extract_file(
        "Mini.agda",
        b"""
module Mini where
open import Agda.Builtin.Nat using (Nat)

data Box : Set where
  box : Nat -> Box

mk : Nat -> Box
mk x = box x
""",
    )
    graph = build_semantic_graph([extraction])
    box = next(
        node for node in graph.nodes.values()
        if node.kind == "constructor" and node.label == "box"
    )
    mk = next(
        node for node in graph.nodes.values()
        if node.kind == "function" and node.label == "mk"
    )
    assert any(
        edge.source == box.symbol_id
        and edge.target == mk.symbol_id
        and edge.kind == "constructs"
        for edge in graph.edges.values()
    )


def test_rhs_binder_use_is_value_flow():
    extraction = extract_file(
        "Mini.agda",
        b"""
module Mini where
open import Agda.Builtin.Nat using (Nat)

idNat : Nat -> Nat
idNat x = x
""",
    )
    graph = build_semantic_graph([extraction])
    owner = next(
        node for node in graph.nodes.values()
        if node.kind == "function" and node.label == "idNat"
    )
    binder = next(
        node for node in graph.nodes.values()
        if node.kind == "binder" and node.label == "x"
    )
    assert any(
        edge.source == binder.symbol_id
        and edge.target == owner.symbol_id
        and edge.kind == "value-flows"
        for edge in graph.edges.values()
    )


def test_prefix_application_emits_argument_flow_to_callee():
    extraction = extract_file(
        "Mini.agda",
        b"""
module Mini where
open import Agda.Builtin.Nat using (Nat)

g : Nat -> Nat
g y = y

f : Nat -> Nat
f x = g x
""",
    )
    graph = build_semantic_graph([extraction])

    g = next(
        node for node in graph.nodes.values()
        if node.kind == "function" and node.label == "g"
    )
    x = next(
        node for node in graph.nodes.values()
        if node.kind == "binder" and node.label == "x"
    )

    assert any(
        edge.source == x.symbol_id
        and edge.target == g.symbol_id
        and edge.kind == "argument-to"
        for edge in graph.edges.values()
    )


def test_constructor_application_emits_argument_flow_to_constructor():
    extraction = extract_file(
        "Mini.agda",
        b"""
module Mini where
open import Agda.Builtin.Nat using (Nat)

data Box : Set where
  box : Nat -> Box

mk : Nat -> Box
mk x = box x
""",
    )
    graph = build_semantic_graph([extraction])

    box = next(
        node for node in graph.nodes.values()
        if node.kind == "constructor" and node.label == "box"
    )
    x = next(
        node for node in graph.nodes.values()
        if node.kind == "binder" and node.label == "x"
    )

    assert any(
        edge.source == x.symbol_id
        and edge.target == box.symbol_id
        and edge.kind == "argument-to"
        for edge in graph.edges.values()
    )


def test_generalized_variables_are_global_nodes_used_by_signatures():
    extraction = extract_file(
        "Mini.agda",
        b"""
module Mini where

variable
  A : Set
  x : A

idA : A -> A
idA y = y
""",
    )
    graph = build_semantic_graph([extraction])

    a = next(
        node for node in graph.nodes.values()
        if node.kind == "variable" and node.label == "A"
    )
    x = next(
        node for node in graph.nodes.values()
        if node.kind == "variable" and node.label == "x"
    )
    id_a = next(
        node for node in graph.nodes.values()
        if node.kind == "function" and node.label == "idA"
    )

    assert a.scope is None
    assert x.scope is None
    assert any(
        edge.source == a.symbol_id
        and edge.target == id_a.symbol_id
        and edge.kind == "type-depends"
        for edge in graph.edges.values()
    )
    assert not any(
        unresolved["reference"] == "A"
        and unresolved["owner"] == id_a.symbol_id
        for unresolved in graph.unresolved_references
    )


def test_lambda_shadowing_creates_distinct_inner_and_outer_binders():
    extraction = extract_file(
        "Mini.agda",
        b"""
module Mini where
open import Agda.Builtin.Nat using (Nat)

outer : Nat -> Nat
outer x = (\\x -> x) x
""",
    )
    graph = build_semantic_graph([extraction])

    owner = next(
        node for node in graph.nodes.values()
        if node.kind == "function" and node.label == "outer"
    )
    xs = [
        node for node in graph.nodes.values()
        if node.kind == "binder" and node.label == "x"
    ]
    assert len(xs) == 2
    assert xs[0].scope != xs[1].scope
    assert xs[0].symbol_id != xs[1].symbol_id

    flowing = {
        edge.source
        for edge in graph.edges.values()
        if edge.target == owner.symbol_id
        and edge.kind == "value-flows"
    }
    assert {node.symbol_id for node in xs}.issubset(flowing)
    assert not any(
        unresolved["reference"] == "x"
        and unresolved["owner"] == owner.symbol_id
        for unresolved in graph.unresolved_references
    )


def test_lambda_scope_falls_back_to_outer_clause_binder():
    extraction = extract_file(
        "Mini.agda",
        b"""
module Mini where
open import Agda.Builtin.Nat using (Nat)

outer : Nat -> Nat
outer x = (\\y -> x) x
""",
    )
    graph = build_semantic_graph([extraction])

    owner = next(
        node for node in graph.nodes.values()
        if node.kind == "function" and node.label == "outer"
    )
    x = next(
        node for node in graph.nodes.values()
        if node.kind == "binder" and node.label == "x"
    )
    y = next(
        node for node in graph.nodes.values()
        if node.kind == "binder" and node.label == "y"
    )

    assert any(
        edge.source == x.symbol_id
        and edge.target == owner.symbol_id
        and edge.kind == "value-flows"
        for edge in graph.edges.values()
    )
    assert not any(
        edge.source == y.symbol_id
        and edge.target == owner.symbol_id
        and edge.kind == "value-flows"
        for edge in graph.edges.values()
    )
    assert not any(
        unresolved["reference"] == "x"
        and unresolved["owner"] == owner.symbol_id
        for unresolved in graph.unresolved_references
    )


def test_where_helper_is_scoped_and_called_from_outer_function():
    extraction = extract_file(
        "Mini.agda",
        b"""
module Mini where
open import Agda.Builtin.Nat using (Nat)

f : Nat -> Nat
f x = g x
  where
    g : Nat -> Nat
    g y = y
""",
    )
    graph = build_semantic_graph([extraction])

    f_node = next(
        node for node in graph.nodes.values()
        if node.kind == "function"
        and node.label == "f"
        and node.scope is None
    )
    g_node = next(
        node for node in graph.nodes.values()
        if node.kind == "function"
        and node.label == "g"
        and node.scope is not None
    )
    x = next(
        node for node in graph.nodes.values()
        if node.kind == "binder" and node.label == "x"
    )
    y = next(
        node for node in graph.nodes.values()
        if node.kind == "binder" and node.label == "y"
    )

    assert g_node.scope is not None
    assert x.scope != y.scope
    assert any(
        edge.source == g_node.symbol_id
        and edge.target == f_node.symbol_id
        and edge.kind == "calls"
        for edge in graph.edges.values()
    )
    assert any(
        edge.source == x.symbol_id
        and edge.target == g_node.symbol_id
        and edge.kind == "argument-to"
        for edge in graph.edges.values()
    )


def test_same_local_helper_name_in_distinct_where_scopes_stays_distinct():
    extraction = extract_file(
        "Mini.agda",
        b"""
module Mini where
open import Agda.Builtin.Nat using (Nat)

f : Nat -> Nat
f x = g x
  where
    g : Nat -> Nat
    g y = y

h : Nat -> Nat
h x = g x
  where
    g : Nat -> Nat
    g y = y
""",
    )
    graph = build_semantic_graph([extraction])

    gs = [
        node for node in graph.nodes.values()
        if node.kind == "function"
        and node.label == "g"
        and node.scope is not None
    ]
    assert len(gs) == 2
    assert gs[0].scope != gs[1].scope
    assert gs[0].symbol_id != gs[1].symbol_id


def test_where_helper_can_capture_outer_pattern_binder():
    extraction = extract_file(
        "Mini.agda",
        b"""
module Mini where
open import Agda.Builtin.Nat using (Nat)

f : Nat -> Nat
f x = g
  where
    g : Nat
    g = x
""",
    )
    graph = build_semantic_graph([extraction])

    g = next(
        node for node in graph.nodes.values()
        if node.kind == "function"
        and node.label == "g"
        and node.scope is not None
    )
    x = next(
        node for node in graph.nodes.values()
        if node.kind == "binder" and node.label == "x"
    )

    assert any(
        edge.source == x.symbol_id
        and edge.target == g.symbol_id
        and edge.kind == "value-flows"
        for edge in graph.edges.values()
    )
    assert not any(
        unresolved["owner"] == g.symbol_id
        and unresolved["reference"] == "x"
        for unresolved in graph.unresolved_references
    )


def test_sibling_where_helper_does_not_see_other_helpers_clause_binder():
    extraction = extract_file(
        "Mini.agda",
        b"""
module Mini where
open import Agda.Builtin.Nat using (Nat)

f : Nat -> Nat
f x = h
  where
    g : Nat -> Nat
    g y = y

    h : Nat
    h = y
""",
    )
    graph = build_semantic_graph([extraction])

    h = next(
        node for node in graph.nodes.values()
        if node.kind == "function"
        and node.label == "h"
        and node.scope is not None
    )

    assert any(
        unresolved["owner"] == h.symbol_id
        and unresolved["reference"] == "y"
        for unresolved in graph.unresolved_references
    )


def test_higher_order_binder_head_is_call_and_receives_argument_flow():
    extraction = extract_file(
        "Mini.agda",
        b"""
module Mini where
open import Agda.Builtin.Nat using (Nat)

apply : (Nat -> Nat) -> Nat -> Nat
apply g x = g x
""",
    )
    graph = build_semantic_graph([extraction])

    apply_node = next(
        node for node in graph.nodes.values()
        if node.kind == "function" and node.label == "apply"
    )
    g = next(
        node for node in graph.nodes.values()
        if node.kind == "binder" and node.label == "g"
    )
    x = next(
        node for node in graph.nodes.values()
        if node.kind == "binder" and node.label == "x"
    )

    assert any(
        edge.source == g.symbol_id
        and edge.target == apply_node.symbol_id
        and edge.kind == "calls"
        for edge in graph.edges.values()
    )
    assert any(
        edge.source == x.symbol_id
        and edge.target == g.symbol_id
        and edge.kind == "argument-to"
        for edge in graph.edges.values()
    )


def test_non_applied_callable_binder_remains_value_flow():
    extraction = extract_file(
        "Mini.agda",
        b"""
module Mini where
open import Agda.Builtin.Nat using (Nat)

keep : (Nat -> Nat) -> (Nat -> Nat)
keep g = g
""",
    )
    graph = build_semantic_graph([extraction])

    keep = next(
        node for node in graph.nodes.values()
        if node.kind == "function" and node.label == "keep"
    )
    g = next(
        node for node in graph.nodes.values()
        if node.kind == "binder" and node.label == "g"
    )

    assert any(
        edge.source == g.symbol_id
        and edge.target == keep.symbol_id
        and edge.kind == "value-flows"
        for edge in graph.edges.values()
    )
    assert not any(
        edge.source == g.symbol_id
        and edge.target == keep.symbol_id
        and edge.kind == "calls"
        for edge in graph.edges.values()
    )


def test_build_semantic_graph_does_not_mutate_cached_extraction_observations():
    extraction = extract_file(
        "Mini.agda",
        b"""
module Mini where
open import Agda.Builtin.Nat using (Nat; zero; suc)

f : Nat -> Nat
f zero = zero
f (suc n) = n
""",
    )
    before = deepcopy(extraction)

    first = build_semantic_graph([extraction])
    after_first = deepcopy(extraction)
    second = build_semantic_graph([extraction])

    assert extraction == before
    assert after_first == before
    assert first.nodes == second.nodes
    assert first.edges == second.edges
    assert first.unresolved_references == second.unresolved_references
    assert first.parse_error_files == second.parse_error_files
