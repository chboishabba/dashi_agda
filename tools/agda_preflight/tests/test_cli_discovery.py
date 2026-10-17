import json

from agda_preflight import interactive_cli


def test_cli_registers_semantic_discovery_commands():
    parser = interactive_cli.build_semantic_parser()
    for argv in (
        ["symbol", "target"],
        ["related", "target"],
        ["object", "DASHI.Core.Foo.target"],
        ["archaeology", "target"],
        ["discover", "target"],
        ["lineage"],
    ):
        args = parser.parse_args(argv)
        assert getattr(args, "command", None) == argv[0]


def test_discovery_json_is_serializable():
    payload = {
        "query": "target",
        "live_matches": [],
        "historical_matches": [],
        "related": {},
        "absence_claim_permitted": True,
    }
    assert json.loads(json.dumps(payload))["absence_claim_permitted"] is True
