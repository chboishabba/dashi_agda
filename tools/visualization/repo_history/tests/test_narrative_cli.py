from dashi_repo_history.narrative import NarrativeEvent
from dashi_repo_history.narrative_cli import build_explanation, build_parser


def test_parser_exposes_history_explain_frontier_stale_archaeology_and_harvest():
    parser = build_parser()
    for command in ("history", "explain", "frontier", "stale", "archaeology", "harvest"):
        argv = [command, "."]
        if command != "harvest":
            argv.append("C3")
        args = parser.parse_args(argv)
        assert args.command == command


def test_explanation_keeps_narrative_authority_explicit_and_surfaces_current_frontier():
    events = [
        NarrativeEvent(
            event_id="commit:1",
            timestamp=1,
            kind="commit",
            title="Old C3 frontier",
            text="Literal C3 action remains open.",
            touched_objects=("DASHI.Physics.C3",),
        ),
        NarrativeEvent(
            event_id="pr:2",
            timestamp=2,
            kind="pull_request",
            title="Recover C3",
            text="Recovered literal C3 action. Actual remaining leaf: A1 covariance. KERNEL-PENDING.",
            pull_request=2,
            touched_objects=("DASHI.Physics.C3",),
        ),
    ]
    payload = build_explanation(events, "C3")
    assert payload["authority"] == "development-narrative"
    assert payload["may_establish_formal_fact"] is False
    assert payload["latest_event"]["event_id"] == "pr:2"
    assert any("A1 covariance" in item for item in payload["current_frontier"])
    assert payload["potentially_stale_frontiers"][0]["event_id"] == "commit:1"
