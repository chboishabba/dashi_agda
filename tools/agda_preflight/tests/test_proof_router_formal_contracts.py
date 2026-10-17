from agda_preflight.proof_router import ProofRouteRequest, ProofRouter


def _absence(query, *, limit=50):
    return {
        "query": query,
        "live_matches": [],
        "historical_matches": [],
        "query_similar": [],
        "related": {
            "signature_equivalent": [],
            "body_equivalent": [],
            "similar": [],
        },
        "absence_claim_permitted": True,
        "absence_status": "confirmed_no_indexed_candidate",
    }


def test_route_names_merged_proof_debt_owner():
    route = ProofRouter(discovery=_absence).route(
        ProofRouteRequest(query="source theorem", target_prover="lean")
    )
    assert route["formal_contracts"]["proof_debt"] == "DASHI.Core.ProofDebtRouterExact"


def test_aristotle_route_names_merged_active_search_owner():
    route = ProofRouter(discovery=_absence).route(
        ProofRouteRequest(query="novel theorem", target_prover="lean")
    )
    assert route["formal_contracts"]["aristotle_search"] == (
        "DASHI.Reasoning.AristotleActiveExperimentalProofSearchLoopExact"
    )
