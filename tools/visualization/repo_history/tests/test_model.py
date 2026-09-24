from dashi_repo_history.model import (
    CommitRecord,
    GraphDelta,
    SemanticGraph,
    SourceSpan,
    Symbol,
)


def test_commit_shape_tracks_merge_parent_count():
    root = CommitRecord("a", 0, ())
    linear = CommitRecord("b", 1, ("a",))
    merge = CommitRecord("c", 2, ("a", "b"))

    assert root.shape == "root"
    assert linear.shape == "linear"
    assert merge.shape == "merge"


def test_binder_scope_changes_identity():
    span = SourceSpan("Mini.agda", 0, 1, 0, 0, 0, 1)
    left = Symbol.create(
        label="x",
        kind="binder",
        module="Mini",
        scope="left-owner",
        span=span,
    )
    right = Symbol.create(
        label="x",
        kind="binder",
        module="Mini",
        scope="right-owner",
        span=span,
    )
    assert left.symbol_id != right.symbol_id


def test_delta_is_set_difference():
    span = SourceSpan("Mini.agda", 0, 1, 0, 0, 0, 1)
    a = Symbol.create(label="a", kind="function", module="Mini", span=span)
    b = Symbol.create(label="b", kind="function", module="Mini", span=span)

    before = SemanticGraph(nodes={a.symbol_id: a})
    after = SemanticGraph(nodes={a.symbol_id: a, b.symbol_id: b})

    delta = GraphDelta.between(before, after)
    assert delta.added_nodes == (b.symbol_id,)
    assert delta.removed_nodes == ()
