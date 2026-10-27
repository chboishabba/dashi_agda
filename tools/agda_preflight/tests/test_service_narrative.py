from types import SimpleNamespace

from agda_preflight.service_semantic_extension import install_service_semantic_extension


class FakeIndex:
    def narrative_archaeology(self, query, *, limit=50):
        return {"query": query, "limit": limit, "matches": [{"event_id": "commit:a"}]}


class FakeService:
    def __init__(self):
        self.index = FakeIndex()


def test_service_exposes_narrative_archaeology():
    install_service_semantic_extension(FakeService)
    service = FakeService()
    result = service.narrative_archaeology("C3", limit=7)
    assert result["query"] == "C3"
    assert result["limit"] == 7
    assert result["matches"][0]["event_id"] == "commit:a"
