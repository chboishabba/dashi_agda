from dashi_repo_history.agda import AgdaLanguageAdapter
from dashi_repo_history.language import LanguageAdapter


def test_agda_adapter_satisfies_language_protocol():
    adapter = AgdaLanguageAdapter()
    assert isinstance(adapter, LanguageAdapter)
    assert adapter.name == "agda"
    assert adapter.suffixes == (".agda",)
