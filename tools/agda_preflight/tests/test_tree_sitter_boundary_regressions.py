from pathlib import Path

from agda_preflight.checker import Checker
from agda_preflight.evidence import EvidenceLevel, policy_for


def write_module(root: Path, module: str, source: str) -> Path:
    path = root.joinpath(*module.split(".")).with_suffix(".agda")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(source, encoding="utf-8")
    return path


def test_constructor_then_field_record_layout_is_known_tree_sitter_gap(tmp_path):
    path = write_module(
        tmp_path,
        "RecordGap",
        """module RecordGap where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

record RuntimeReceipt (enabled : Bool) : Set where
  constructor runtime-receipt
  field
    rank : Nat
    label : String
    agrees : Bool
""",
    )

    diagnostics = Checker(tmp_path).check(path)

    assert not any(d.code == "TSAGDA000" for d in diagnostics)


def test_qualified_record_assignment_remains_a_hard_syntax_error(tmp_path):
    path = write_module(
        tmp_path,
        "QualifiedField",
        """module QualifiedField where

record Tower : Set₁ where
  field
    Point : Set

bad : Tower
bad = record { Tower.Point = Set }
""",
    )

    hits = [d for d in Checker(tmp_path).check(path) if d.code == "TSAGDA090"]

    assert hits
    assert all(d.severity == "error" for d in hits)
    assert policy_for("TSAGDA090").minimum == EvidenceLevel.TREE_SITTER


def test_visible_imported_projection_receiver_does_not_emit_missing_receiver(tmp_path):
    write_module(
        tmp_path,
        "Render",
        """module Render where

open import Agda.Builtin.Nat using (Nat)

record JPhaseRenderingAlgebra : Set where
  field
    klein : Nat
""",
    )
    path = write_module(
        tmp_path,
        "UseRender",
        """module UseRender where

open import Agda.Builtin.Nat using (Nat)
import Render as Render

render : Render.JPhaseRenderingAlgebra → Nat
render R = Render.klein R
""",
    )

    diagnostics = Checker(tmp_path).check(path)

    assert not any(d.code in {"TSAGDA049", "TSAGDA052"} for d in diagnostics)


def test_projection_receiver_diagnostics_require_agda_scope_evidence():
    assert policy_for("TSAGDA049").minimum == EvidenceLevel.AGDA_SCOPE
    assert policy_for("TSAGDA052").minimum == EvidenceLevel.AGDA_SCOPE


def test_equality_value_diagnostic_requires_typechecker_evidence():
    policy = policy_for("TSAGDA104")
    assert policy.minimum == EvidenceLevel.AGDA_TYPECHECKER
    assert policy.hard_error_allowed is False


def test_imported_constructor_shadow_is_predicted_at_user_authored_binders(tmp_path):
    write_module(
        tmp_path,
        "Cube",
        """module Cube where

data Pair (A B : Set) : Set where
  pair : A → B → Pair A B
""",
    )
    path = write_module(
        tmp_path,
        "Shadow",
        """module Shadow where

open import Agda.Builtin.List using (List; []; _∷_)
import Cube as Cube

first : {A B : Set} → Cube.Pair A B → A
first (Cube.pair a b) = a

use : {A B : Set} → Cube.Pair A B → Cube.Pair A B
use pair = pair

walk : {A B : Set} → List (Cube.Pair A B) → List (Cube.Pair A B)
walk [] = []
walk (pair ∷ pairs) = pair ∷ walk pairs
""",
    )

    hits = [d for d in Checker(tmp_path).check(path) if d.code == "TSAGDA300"]

    assert hits
    assert all(d.severity == "warning" for d in hits)
    assert all(d.evidence == "dashi-index" for d in hits)
    assert {d.line for d in hits} == {9, 13}
    assert all("Cube.pair" in d.message for d in hits)
    # Constructor use itself is not a binder shadow.
    assert not any(d.line == 6 for d in hits)
