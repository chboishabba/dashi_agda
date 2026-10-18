from dashi_repo_history.agda import build_semantic_graph, extract_file
from dashi_repo_history.semantic_backend import PythonAffectedModuleBackend


def _file(path: str, source: str):
    return extract_file(path, source.encode("utf-8"))


def test_python_backend_matches_full_rebuild():
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
foo : Set
foo = Set
baz : Set
baz = foo
""",
        ),
        before[1],
    ]

    backend = PythonAffectedModuleBackend()
    previous = build_semantic_graph(before)
    result = backend.patch(
        previous=previous,
        before=before,
        after=after,
        changed_paths=["A.agda"],
    )
    rebuilt = build_semantic_graph(after)

    assert result.graph.nodes == rebuilt.nodes
    assert result.graph.edges == rebuilt.edges
    assert result.plan.affected_modules == ("A", "B")
    assert result.plan_ns >= 0
    assert result.patch_ns >= 0
