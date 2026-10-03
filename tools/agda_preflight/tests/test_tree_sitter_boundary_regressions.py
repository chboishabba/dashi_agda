from pathlib import Path

from agda_preflight.checker import Checker
from agda_preflight.evidence import EvidenceLevel, policy_for


def write_module(root: Path, module: str, source: str) -> Path:
    """Write one repository-shaped Agda module under ROOT."""

    path = root.joinpath(*module.split(".")).with_suffix(".agda")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(source, encoding="utf-8")
    return path


def test_constructor_then_field_record_layout_is_known_tree_sitter_gap(tmp_path):
    """Valid Agda records must not need eta-equality to placate tree-sitter."""

    modules = (
        "DASHI.Moonshine.OggSSP2BIntegralMoonshineLocalActionSourceExact",
        "DASHI.Moonshine.OggSSP2BTateGradingConventionBridgeExact",
    )
    for module in modules:
        path = write_module(
            tmp_path,
            module,
            f"""module {module} where

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
    """The real Agda parser mismatch TSAGDA090 stays hard at syntax evidence."""

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
    """An Agda-accepted `Render.klein R` shape must not be called receiverless."""

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
    """Ambiguous projection receiver claims cannot be hard at index evidence."""

    assert policy_for("TSAGDA049").minimum == EvidenceLevel.AGDA_SCOPE
    assert policy_for("TSAGDA052").minimum == EvidenceLevel.AGDA_SCOPE


def test_equality_value_diagnostic_requires_typechecker_evidence():
    """Proof-vs-value classification is a typing judgment when aliases intervene."""

    policy = policy_for("TSAGDA104")
    assert policy.minimum == EvidenceLevel.AGDA_TYPECHECKER
    assert policy.hard_error_allowed is False


def test_imported_constructor_shadow_is_predicted_at_user_authored_binders(tmp_path):
    """A non-open imported constructor can soundly drive TSAGDA300 prediction."""

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
    assert {d.line for d in hits} == {10, 14}
    assert all("Cube.pair" in d.message for d in hits)
    assert not any(d.line == 7 for d in hits)


def test_opened_constructor_is_not_guessed_to_be_a_shadowing_binder(tmp_path):
    """Opened constructors remain ambiguous and are left to Agda scope checking."""

    write_module(
        tmp_path,
        "OpenedCube",
        """module OpenedCube where

data Pair (A B : Set) : Set where
  pair : A → B → Pair A B
""",
    )
    path = write_module(
        tmp_path,
        "OpenedUse",
        """module OpenedUse where

open import OpenedCube

first : {A B : Set} → Pair A B → A
first (pair a b) = a
""",
    )

    hits = [d for d in Checker(tmp_path).check(path) if d.code == "TSAGDA300"]

    assert hits == []
