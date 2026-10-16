from agda_preflight.mcp_server import register_mcp_tools


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


def test_mcp_registers_semantic_discovery_tools():
    server = FakeServer()
    register_mcp_tools(server, FakeService())
    for name in (
        "symbol_search",
        "related_symbols",
        "object_detail",
        "narrative_archaeology",
        "discover",
        "round_lineage",
    ):
        assert name in server.names
