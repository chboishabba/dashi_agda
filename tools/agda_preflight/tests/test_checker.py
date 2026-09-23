from pathlib import Path

from agda_preflight.checker import Checker


def write_module(root: Path, module: str, source: str) -> Path:
    path = root.joinpath(*module.split(".")).with_suffix(".agda")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(source, encoding="utf-8")
    return path


def test_unapplied_record_projection_used_as_sort(tmp_path):
    path = write_module(
        tmp_path,
        "Bug",
        """module Bug where

record Model : Set₁ where
  field
    Parameter : Set
    Scalar : Set

open Model public

Series :
  Model → Parameter → Scalar
Series M x = x
""",
    )
    diagnostics = Checker(tmp_path).check(path)
    assert any(d.code == "TSAGDA001" and "Parameter" in d.message for d in diagnostics)


def test_applied_record_projection_is_not_flagged(tmp_path):
    path = write_module(
        tmp_path,
        "Good",
        """module Good where

record Model : Set₁ where
  field
    Parameter : Set
    Scalar : Set

open Model public

Series :
  (M : Model) → Parameter M → Scalar M
Series M x = x
""",
    )
    diagnostics = Checker(tmp_path).check(path)
    assert not any(d.code == "TSAGDA001" for d in diagnostics)


def test_record_field_terminal_kind_mismatch(tmp_path):
    path = write_module(
        tmp_path,
        "GateBug",
        """module GateBug where

data ⊤ : Set where
  tt : ⊤

record Source : Set₁ where
  field
    coefficientAgreement : (n : Nat) → ⊤

open Source public

record Target : Set₁ where
  field
    coefficientAgreement : (n : Nat) → Set

open Target public

adapt :
  (A : Source) →
  Target
adapt A =
  record
    { coefficientAgreement = λ n → coefficientAgreement A n
    }
""",
    )
    diagnostics = Checker(tmp_path).check(path)
    hits = [d for d in diagnostics if d.code == "TSAGDA003"]
    assert hits
    assert "Set" in hits[0].message
    assert "⊤" in hits[0].message


def test_reverse_import_frontier(tmp_path):
    leaf = write_module(tmp_path, "A.Leaf", "module A.Leaf where\n")
    write_module(
        tmp_path,
        "A.Middle",
        "module A.Middle where\n\nimport A.Leaf\n",
    )
    write_module(
        tmp_path,
        "A.Top",
        "module A.Top where\n\nimport A.Middle\n",
    )
    plan = Checker(tmp_path).affected_modules(leaf)
    assert plan[:3] == ["A.Leaf", "A.Middle", "A.Top"]
