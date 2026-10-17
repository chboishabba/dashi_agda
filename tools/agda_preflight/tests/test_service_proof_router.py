import sqlite3

from agda_preflight.service_semantic_extension import install_service_semantic_extension


class FakeIndex:
    def __init__(self):
        self.connection = sqlite3.connect(":memory:")
        self.connection.row_factory = sqlite3.Row
        self.connection.execute(
            "CREATE TABLE repository_meta(key TEXT PRIMARY KEY, value TEXT NOT NULL)"
        )

    def discovery_receipt(self, query, *, limit=50):
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


class FakeService:
    def __init__(self):
        self.index = FakeIndex()
        self.semantic = None


install_service_semantic_extension(FakeService)


def test_service_routes_confirmed_absence_to_aristotle():
    service = FakeService()
    result = service.proof_route("new theorem", target_prover="lean")
    assert result["recommended_backend"] == "aristotle+lean"
    assert result["authority"] == "routing-only"


def test_service_resolves_da51_without_promoting_status():
    service = FakeService()
    result = service.da51_resolve("0xDA51800100000000")
    assert result["atlas"]["status"] == 1
    assert result["authority"] == "identity-only"
    assert result["establishes_proof"] is False
