from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))

from _stranded_common import closure, family_of, is_round


def test_round_recognition():
    assert is_round("DASHI.X.Round604Exact")
    assert not is_round("DASHI.X.Canonical")


def test_family():
    assert family_of("DASHI.X.FooRound604Exact") == "DASHI.X.Foo"


def test_closure():
    imports = {"A": {"B", "C"}, "B": {"D"}}
    assert closure(imports, ["A"], {"A", "B", "C", "D"}) == {
        "A",
        "B",
        "C",
        "D",
    }
