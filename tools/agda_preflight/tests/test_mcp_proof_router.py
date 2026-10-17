from agda_preflight.mcp_adapter import DashiAgdaMcpTools
from agda_preflight.mcp_semantic_extension import install_mcp_adapter_semantic_extension


class FakeService:
    def proof_route(self, query, **kwargs):
        return {"query": query, "recommended_backend": "aristotle+lean", "authority": "routing-only"}

    def proof_route_history(self, **kwargs):
        return {"routes": [], "authority": "routing-only"}

    def da51_resolve(self, address):
        return {"address": address, "authority": "identity-only"}

    def da51_evidence(self, address):
        return {"address": address, "evidence": [], "authority": "evidence-only"}

    def da51_frontier(self, address):
        return {"address": address, "routes": [], "authority": "routing-only"}


install_mcp_adapter_semantic_extension(DashiAgdaMcpTools)


def test_repository_mcp_adapter_exposes_proof_route():
    tools = DashiAgdaMcpTools(FakeService())
    result = tools.proof_route("goal", target_prover="lean")
    assert result["recommended_backend"] == "aristotle+lean"
    assert result["authority"] == "routing-only"


def test_repository_mcp_adapter_exposes_da51_read_surfaces():
    tools = DashiAgdaMcpTools(FakeService())
    assert tools.da51_resolve("0xDA51800100000000")["authority"] == "identity-only"
    assert tools.da51_evidence("0xDA51800100000000")["authority"] == "evidence-only"
    assert tools.da51_frontier("0xDA51800100000000")["authority"] == "routing-only"
