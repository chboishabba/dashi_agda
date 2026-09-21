from dashi_repo_history.agda import build_semantic_graph, extract_file
from dashi_repo_history.incremental import (
    ResolutionImpactIndex,
    patch_semantic_graph,
    plan_incremental_impact,
    plan_incremental_impact_indexed,
)


def _file(path: str, source: str):
    return extract_file(path, source.encode("utf-8"))


def test_incremental_patch_matches_full_rebuild_for_local_change():
    before = [
        _file(
            "A.agda",
            """
module A where
foo : Set
foo = Set
""",
        ),
        _file(
            "B.agda",
            """
module B where
bar : Set
bar = Set
""",
        ),
    ]
    after = [
        _file(
            "A.agda",
            """
module A where
foo : Set
foo = Set
new : Set
new = foo
""",
        ),
        before[1],
    ]

    previous = build_semantic_graph(before)
    plan = plan_incremental_impact(before, after, ["A.agda"])
    patched, receipt = patch_semantic_graph(
        previous,
        before,
        after,
        plan,
    )
    rebuilt = build_semantic_graph(after)

    assert plan.affected_modules == ("A",)
    assert patched.graph_id == rebuilt.graph_id
    assert patched.nodes == rebuilt.nodes
    assert patched.edges == rebuilt.edges
    assert receipt.affected_modules == ("A",)


def test_open_importer_is_rebuilt_when_exported_symbol_changes():
    before = [
        _file(
            "A.agda",
            """
module A where
foo : Set
foo = Set
""",
        ),
        _file(
            "B.agda",
            """
module B where
open import A
bar : Set
bar = foo
""",
        ),
    ]
    after = [
        _file(
            "A.agda",
            """
module A where
foo2 : Set
foo2 = Set
""",
        ),
        before[1],
    ]

    previous = build_semantic_graph(before)
    plan = plan_incremental_impact(before, after, ["A.agda"])
    patched, _receipt = patch_semantic_graph(
        previous,
        before,
        after,
        plan,
    )
    rebuilt = build_semantic_graph(after)

    assert plan.affected_modules == ("A", "B")
    assert patched.graph_id == rebuilt.graph_id

    bar = next(
        node
        for node in patched.nodes.values()
        if node.module == "B" and node.label == "bar"
    )
    assert any(
        observation["owner"] == bar.symbol_id
        and observation["reference"] == "foo"
        for observation in patched.unresolved_references
    )


def test_plain_importer_is_conservatively_rebuilt():
    before = [
        _file(
            "A.agda",
            """
module A where
foo : Set
foo = Set
""",
        ),
        _file(
            "B.agda",
            """
module B where
import A
bar : Set
bar = A.foo
""",
        ),
    ]
    after = [
        _file(
            "A.agda",
            """
module A where
foo2 : Set
foo2 = Set
""",
        ),
        before[1],
    ]

    plan = plan_incremental_impact(before, after, ["A.agda"])

    assert plan.affected_modules == ("A", "B")
    assert any(
        reason.startswith("imports-changed-module:A")
        for module, reason in plan.reasons
        if module == "B"
    )


def test_unrelated_module_is_reused_not_regenerated():
    before = [
        _file(
            "A.agda",
            """
module A where
foo : Set
foo = Set
""",
        ),
        _file(
            "C.agda",
            """
module C where
c : Set
c = Set
""",
        ),
    ]
    after = [
        _file(
            "A.agda",
            """
module A where
foo2 : Set
foo2 = Set
""",
        ),
        before[1],
    ]

    previous = build_semantic_graph(before)
    c_before = next(
        node
        for node in previous.nodes.values()
        if node.module == "C" and node.label == "c"
    )

    plan = plan_incremental_impact(before, after, ["A.agda"])
    patched, _receipt = patch_semantic_graph(
        previous,
        before,
        after,
        plan,
    )

    c_after = patched.nodes[c_before.symbol_id]
    assert c_after == c_before
    assert "C" not in plan.affected_modules


def test_deleted_module_removes_its_fragment_and_rebuilds_importer():
    before = [
        _file(
            "A.agda",
            """
module A where
foo : Set
foo = Set
""",
        ),
        _file(
            "B.agda",
            """
module B where
open import A
bar : Set
bar = foo
""",
        ),
    ]
    after = [before[1]]

    previous = build_semantic_graph(before)
    plan = plan_incremental_impact(before, after, ["A.agda"])
    patched, _receipt = patch_semantic_graph(
        previous,
        before,
        after,
        plan,
    )
    rebuilt = build_semantic_graph(after)

    assert plan.affected_modules == ("A", "B")
    assert patched.graph_id == rebuilt.graph_id
    assert not any(node.module == "A" for node in patched.nodes.values())


def test_indexed_impact_plan_matches_scanning_plan():
    before = [
        _file(
            "A.agda",
            """
module A where
foo : Set
foo = Set
""",
        ),
        _file(
            "B.agda",
            """
module B where
open import A
bar : Set
bar = foo
""",
        ),
        _file(
            "C.agda",
            """
module C where
import A
c : Set
c = A.foo
""",
        ),
        _file(
            "D.agda",
            """
module D where
d : Set
d = Set
""",
        ),
    ]
    after = [
        _file(
            "A.agda",
            """
module A where
foo2 : Set
foo2 = Set
""",
        ),
        before[1],
        before[2],
        before[3],
    ]

    scanning = plan_incremental_impact(
        before,
        after,
        ["A.agda"],
    )
    before_index = ResolutionImpactIndex.from_files(before)
    after_index = before_index.fork_apply(
        {file.path: file for file in after},
        ["A.agda"],
    )
    indexed = plan_incremental_impact_indexed(
        before_index,
        after_index,
        ["A.agda"],
    )

    assert indexed == scanning
    assert indexed.affected_modules == ("A", "B", "C")
    assert "D" not in indexed.affected_modules


def test_indexed_impact_plan_handles_deleted_module():
    before = [
        _file(
            "A.agda",
            """
module A where
foo : Set
foo = Set
""",
        ),
        _file(
            "B.agda",
            """
module B where
open import A
bar : Set
bar = foo
""",
        ),
    ]
    after = [before[1]]

    scanning = plan_incremental_impact(
        before,
        after,
        ["A.agda"],
    )
    before_index = ResolutionImpactIndex.from_files(before)
    after_index = before_index.fork_apply(
        {file.path: file for file in after},
        ["A.agda"],
    )
    indexed = plan_incremental_impact_indexed(
        before_index,
        after_index,
        ["A.agda"],
    )

    assert indexed == scanning
    assert indexed.changed_modules == ("A",)
    assert indexed.affected_modules == ("A", "B")


def test_index_update_removes_stale_reverse_dependencies():
    before = [
        _file(
            "A.agda",
            """
module A where
foo : Set
foo = Set
""",
        ),
        _file(
            "B.agda",
            """
module B where
open import A
bar : Set
bar = foo
""",
        ),
    ]
    after = [
        before[0],
        _file(
            "B.agda",
            """
module B where
bar : Set
bar = Set
""",
        ),
    ]

    before_index = ResolutionImpactIndex.from_files(before)
    after_index = before_index.fork_apply(
        {file.path: file for file in after},
        ["B.agda"],
    )

    assert "B" in before_index.openers_by_target["A"]
    assert "B" not in after_index.openers_by_target.get(
        "A",
        frozenset(),
    )
