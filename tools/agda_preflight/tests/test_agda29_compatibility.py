from pathlib import Path

from agda_preflight.checker import Checker
from agda_preflight.evidence import EvidenceLevel, policy_for


def write_module(root: Path, module: str, source: str) -> Path:
    path = root.joinpath(*module.split(".")).with_suffix(".agda")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(source, encoding="utf-8")
    return path


def test_lean_style_reverse_rewrite_is_hard_syntax_error(tmp_path):
    path = write_module(
        tmp_path,
        "ReverseRewrite",
        """module ReverseRewrite where

open import Agda.Builtin.Equality using (_≡_; refl)

f : {A : Set} {x y : A} → x ≡ y → y ≡ x
f p rewrite <- p = refl
""",
    )
    hits = [d for d in Checker(tmp_path).check(path) if d.code == "TSAGDA000"]
    assert any("reverse rewrite" in d.message for d in hits)
    assert all(d.severity == "error" for d in hits)


def test_nonconstructor_rewrite_argument_predicts_rewrites_nothing(tmp_path):
    path = write_module(
        tmp_path,
        "FragileRewrite",
        """module FragileRewrite where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

flattenRound : Nat → Nat
flattenRound n = n

roundTrip : (n : Nat) → flattenRound n ≡ n
roundTrip n = refl

fragile : (state : Nat) → flattenRound state ≡ state
fragile state rewrite roundTrip (flattenRound state) = refl
""",
    )
    hits = [d for d in Checker(tmp_path).check(path) if d.code == "TSAGDA301"]
    assert hits
    assert all(d.severity == "warning" for d in hits)
    assert all(d.evidence == "dashi-index" for d in hits)
    assert any("flattenRound state" in d.message for d in hits)


def test_constructor_destructuring_rewrite_is_not_predicted_as_rewrites_nothing(tmp_path):
    path = write_module(
        tmp_path,
        "ConstructorRewrite",
        """module ConstructorRewrite where

open import Agda.Builtin.Equality using (_≡_; refl)

data Box : Set where
  box : Box

stable : Box → Box
stable box rewrite refl = box
""",
    )
    assert not any(
        d.code == "TSAGDA301" and "non-constructor" in d.message
        for d in Checker(tmp_path).check(path)
    )


def test_wrong_named_implicit_position_is_reported(tmp_path):
    path = write_module(
        tmp_path,
        "WrongHiding",
        """module WrongHiding where

open import Agda.Builtin.Nat using (Nat)

f : (symmetry : Nat) → {left right : Nat} → Nat → Nat
f {left = left} symmetry {right = right} value = value
""",
    )
    hits = [
        d for d in Checker(tmp_path).check(path)
        if d.code == "TSAGDA043" and "named implicit" in d.message
    ]
    assert hits
    assert all(d.severity == "warning" for d in hits)


def test_correct_named_implicit_position_is_not_reported(tmp_path):
    path = write_module(
        tmp_path,
        "RightHiding",
        """module RightHiding where

open import Agda.Builtin.Nat using (Nat)

f : (symmetry : Nat) → {left right : Nat} → Nat → Nat
f symmetry {left = left} {right = right} value = value
""",
    )
    assert not any(
        d.code == "TSAGDA043" and "named implicit" in d.message
        for d in Checker(tmp_path).check(path)
    )


def test_equality_operands_do_not_trigger_type_head_term_diagnostics(tmp_path):
    path = write_module(
        tmp_path,
        "EqualityOperand",
        """module EqualityOperand where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

uncurlSix : Nat → Nat
uncurlSix n = n

record Exact : Set where
  field
    agrees : (h : Nat) → uncurlSix h ≡ h
""",
    )
    assert not any(
        d.code in {"TSAGDA120", "TSAGDA123"}
        for d in Checker(tmp_path).check(path)
    )


def test_rewrites_nothing_is_dual_source_index_diagnostic():
    assert policy_for("TSAGDA301").minimum == EvidenceLevel.DASHI_INDEX


def test_accepted_carrier_adapter_claim_requires_typechecker_evidence():
    policy = policy_for("TSAGDA206")
    assert policy.minimum == EvidenceLevel.AGDA_TYPECHECKER
    assert policy.hard_error_allowed is False


def test_alias_collision_claim_requires_scope_evidence():
    assert policy_for("TSAGDA028").minimum == EvidenceLevel.AGDA_SCOPE
