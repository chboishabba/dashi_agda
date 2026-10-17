from agda_preflight.mcp_adapter import DashiAgdaMcpTools
from agda_preflight.mcp_semantic_extension import install_mcp_adapter_semantic_extension


class FakeService:
    def proof_route(self, query, **kwargs):
        return {"query": query, "recommended_backend": "aristotle+lean", "authority": "routing-only"}

    def proof_route_for_obligation(self, query, **kwargs):
        return {
            "query": query,
            "demand_ref": kwargs["demand_ref"],
            "external_obligation_ref": kwargs["external_obligation_ref"],
            "statement_digest": kwargs["statement_digest"],
            "recommended_backend": "aristotle+lean",
            "authority": "routing-only",
            "establishes_proof": False,
        }

    def formal_evidence_for_obligation(self, **kwargs):
        return {**kwargs, "evidence": [], "authority": "evidence-only", "establishes_proof": False}

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


def test_repository_mcp_adapter_exposes_external_obligation_route_and_evidence():
    tools = DashiAgdaMcpTools(FakeService())
    route = tools.proof_route_for_obligation(
        "goal",
        demand_ref="formal-demand:1",
        external_obligation_ref="proof-obligation:1",
        statement_digest="sha256:a",
    )
    assert route["demand_ref"] == "formal-demand:1"
    assert route["establishes_proof"] is False
    evidence = tools.formal_evidence_for_obligation(
        demand_ref="formal-demand:1",
        external_obligation_ref="proof-obligation:1",
        statement_digest="sha256:a",
    )
    assert evidence["evidence"] == []
    assert evidence["establishes_proof"] is False


def test_repository_mcp_adapter_exposes_da51_read_surfaces():
    tools = DashiAgdaMcpTools(FakeService())
    assert tools.da51_resolve("0xDA51800100000000")["authority"] == "identity-only"
    assert tools.da51_evidence("0xDA51800100000000")["authority"] == "evidence-only"
    assert tools.da51_frontier("0xDA51800100000000")["authority"] == "routing-only"
