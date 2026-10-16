from agda_preflight.mcp_server import register_repository_mcp_tools


class FakeServer:
    def __init__(self):
        self.names = []

    def tool(self):
        def decorate(fn):
            self.names.append(fn.__name__)
            return fn
        return decorate


class FakeService:
    pass


def test_repository_mcp_registers_semantic_and_history_tools():
    server = FakeServer()
    register_repository_mcp_tools(server, FakeService())
    for name in (
        "symbol_search",
        "related_symbols",
        "object_detail",
        "narrative_archaeology",
        "narrative_history",
        "narrative_frontier",
        "narrative_stale",
        "narrative_explain",
        "discover",
        "round_lineage",
    ):
        assert name in server.names
