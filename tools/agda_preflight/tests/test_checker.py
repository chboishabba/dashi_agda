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


def test_unresolved_projection_receiver_is_reported(tmp_path):
    write_module(
        tmp_path,
        "Pareto",
        """module Pareto where

record Costs : Set₁ where
  field
    Axis : Set
    cost : Axis → Nat → Nat
""",
    )
    broken = write_module(
        tmp_path,
        "Broken",
        """module Broken where

import Pareto as Pareto

projected :
  {costs : Pareto.Costs} →
  Pareto.Axis costs → Nat → Nat
projected axis value = Pareto.cost _ axis value
""",
    )
    good = write_module(
        tmp_path,
        "GoodReceiver",
        """module GoodReceiver where

import Pareto as Pareto

projected :
  {costs : Pareto.Costs} →
  Pareto.Axis costs → Nat → Nat
projected {costs} axis value = Pareto.cost costs axis value
""",
    )
    broken_hits = [d for d in Checker(tmp_path).check(broken) if d.code == "TSAGDA002"]
    assert broken_hits
    assert "costs" in broken_hits[0].hint
    assert not any(d.code == "TSAGDA002" for d in Checker(tmp_path).check(good))


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


def test_known_grammar_gaps_do_not_mask_real_syntax_errors(tmp_path):
    valid = write_module(
        tmp_path,
        "Valid",
        """module Valid where

import Agda.Builtin.Bool as ℚP

record Receipt : Set where
  constructor receipt
  field
    accepted : ℚP.Bool

record ParameterizedReceipt (n : Nat) : Set where
  constructor parameterized-receipt
  field
    acceptedAgain : ℚP.Bool
""",
    )
    invalid = write_module(
        tmp_path,
        "Invalid",
        """module Invalid where

broken : Set
broken = {
""",
    )
    assert not any(d.code == "TSAGDA000" for d in Checker(tmp_path).check(valid))
    assert any(d.code == "TSAGDA000" for d in Checker(tmp_path).check(invalid))


def test_module_path_mismatch(tmp_path):
    path = write_module(tmp_path, "Right.Name", "module Wrong.Name where\n")
    hits = Checker(tmp_path).check(path)
    assert any(d.code == "TSAGDA004" for d in hits)


def test_unknown_using_name_is_reported(tmp_path):
    write_module(tmp_path, "Lib", "module Lib where\n\nx : Set\nx = Set\n")
    path = write_module(
        tmp_path,
        "Use",
        "module Use where\n\nopen import Lib using (missing)\n",
    )
    hits = Checker(tmp_path).check(path)
    assert any(d.code == "TSAGDA023" for d in hits)


def test_clause_arity_mismatch_is_reported(tmp_path):
    path = write_module(
        tmp_path,
        "Arity",
        """module Arity where

f : Set → Set → Set
f x = x
""",
    )
    hits = Checker(tmp_path).check(path)
    assert any(d.code == "TSAGDA045" for d in hits)


def test_record_unknown_and_missing_fields_are_reported(tmp_path):
    path = write_module(
        tmp_path,
        "Records",
        """module Records where

record R : Set₁ where
  field
    A : Set
    B : Set

mk : R
mk =
  record
    { A = Set
    ; C = Set
    }
""",
    )
    hits = Checker(tmp_path).check(path)
    assert any(d.code == "TSAGDA060" for d in hits)
    assert any(d.code == "TSAGDA062" for d in hits)


def test_obvious_negative_occurrence_is_reported(tmp_path):
    path = write_module(
        tmp_path,
        "Negative",
        """module Negative where

data Bad : Set where
  bad : (Bad → Set) → Bad
""",
    )
    hits = Checker(tmp_path).check(path)
    assert any(d.code in {"TSAGDA130", "TSAGDA131"} for d in hits)


def test_unsafe_pragmas_are_reported(tmp_path):
    path = write_module(
        tmp_path,
        "UnsafeExact",
        """module UnsafeExact where

{-# TERMINATING #-}
loop : Set
loop = loop
""",
    )
    hits = Checker(tmp_path).check(path)
    assert any(d.code == "TSAGDA161" for d in hits)


def test_api_snapshot_detects_constructor_arity_drift(tmp_path):
    from agda_preflight.rules import api_snapshot, api_drift
    from agda_preflight.checker import Diagnostic

    path = write_module(
        tmp_path,
        "Api",
        """module Api where

data D : Set where
  c : Set → D
""",
    )
    checker = Checker(tmp_path)
    baseline = api_snapshot(checker)
    path.write_text(
        """module Api where

data D : Set where
  c : Set → Set → D
""",
        encoding="utf-8",
    )
    checker = Checker(tmp_path)
    hits = api_drift(checker, baseline, Diagnostic)
    assert any(d.code == "TSAGDA182" for d in hits)


def test_core_frontend_does_not_use_regex_as_parser():
    package = Path(__file__).parents[1] / "agda_preflight"
    for name in ("checker.py", "rules.py", "ast_index.py", "shapes.py"):
        source = (package / name).read_text(encoding="utf-8")
        assert "import re" not in source
        assert "from re import" not in source


def test_ast_index_recovers_import_alias_and_record_fields(tmp_path):
    write_module(
        tmp_path,
        "Lib",
        """module Lib where

record R : Set₁ where
  field
    A : Set
    x : A
""",
    )
    path = write_module(
        tmp_path,
        "Use",
        """module Use where

import Lib as L

open L.R public
""",
    )
    summary = Checker(tmp_path).parse_summary(path)
    assert summary.imports["L"] == "Lib"


def test_ast_record_expression_index(tmp_path):
    path = write_module(
        tmp_path,
        "RecordExpr",
        """module RecordExpr where

record R : Set₁ where
  field
    A : Set
    B : Set

mk : R
mk = record
  { A = Set
  ; B = Set
  }
""",
    )
    summary = Checker(tmp_path).parse_summary(path)
    assert summary.ast.record_expressions
    assert {a.name for a in summary.ast.record_expressions[0].assignments} == {"A", "B"}



def test_dependency_modules_does_not_build_global_graph(tmp_path):
    leaf = write_module(tmp_path, "A.Leaf", "module A.Leaf where\n")
    top = write_module(
        tmp_path,
        "A.Top",
        "module A.Top where\n\nimport A.Leaf\n",
    )
    checker = Checker(tmp_path)

    def forbidden():
        raise AssertionError("dependency_modules must not build the repository-wide graph")

    checker.dependency_graph = forbidden
    assert checker.dependency_modules(top) == ["A.Leaf", "A.Top"]


def test_per_module_check_does_not_build_global_graph(tmp_path):
    leaf = write_module(tmp_path, "A.Leaf", "module A.Leaf where\n")
    top = write_module(
        tmp_path,
        "A.Top",
        "module A.Top where\n\nimport A.Leaf\n",
    )
    checker = Checker(tmp_path)

    def forbidden():
        raise AssertionError("per-module diagnostics must stay inside the import cone")

    checker.dependency_graph = forbidden
    checker.check(top)


def test_data_constructor_index_uses_node_equality(tmp_path):
    path = write_module(
        tmp_path,
        "DataIndex",
        """module DataIndex where

data D : Set where
  c : Set → D
""",
    )
    summary = Checker(tmp_path).parse_summary(path)
    assert "D" in summary.ast.data
    assert "c" in summary.ast.data["D"].constructors


def test_record_fields_are_recovered_from_tree_sitter_siblings(tmp_path):
    path = write_module(
        tmp_path,
        "SiblingRecord",
        """module SiblingRecord where

record R : Set₁ where
  constructor r
  field
    A : Set
    x : A
""",
    )
    summary = Checker(tmp_path).parse_summary(path)
    assert "R" in summary.ast.records
    record = summary.ast.records["R"]
    assert record.constructor == "r"
    assert set(record.fields) == {"A", "x"}


def test_reserved_keywords_are_not_function_clause_names(tmp_path):
    path = write_module(
        tmp_path,
        "Keywords",
        """module Keywords where

record R : Set where
  constructor r
  field
    A : Set
""",
    )
    summary = Checker(tmp_path).parse_summary(path)
    assert not ({"where", "as", "constructor", "field"} & set(summary.ast.clauses))
    assert not ({"where", "as", "constructor", "field"} & set(summary.ast.signatures))



def test_shape_preserves_telescope_before_equality_result(tmp_path):
    from agda_preflight.shapes import (
        PiShape,
        equality_shape,
        explicit_arity,
        shape_from_node,
    )

    path = write_module(
        tmp_path,
        "EqualityTelescope",
        """module EqualityTelescope where

ι²-id :
  ∀ {X} (s : State X) (x : X) →
  apply (ι (ι s)) x ≡ apply s x
""",
    )
    summary = Checker(tmp_path).parse_summary(path)
    signature = summary.ast.signatures["ι²-id"]
    shape = shape_from_node(summary.ast.source_bytes, signature.type_node)
    assert isinstance(shape, PiShape)
    assert explicit_arity(shape) == 2
    assert equality_shape(shape) is not None


def test_grouped_telescope_binders_count_individually(tmp_path):
    from agda_preflight.shapes import explicit_arity, shape_from_node

    path = write_module(
        tmp_path,
        "GroupedTelescope",
        """module GroupedTelescope where

f : (A B : Set) → A → B → Set
""",
    )
    summary = Checker(tmp_path).parse_summary(path)
    signature = summary.ast.signatures["f"]
    shape = shape_from_node(summary.ast.source_bytes, signature.type_node)
    assert explicit_arity(shape) == 4


def test_horizontal_dividers_are_not_function_clauses(tmp_path):
    path = write_module(
        tmp_path,
        "Dividers",
        """module Dividers where

------------------------------------------------------------------------
-- Section

x : Set
x = Set
------------------------------------------------------------------------
""",
    )
    summary = Checker(tmp_path).parse_summary(path)
    assert set(summary.ast.clauses) == {"x"}
    assert not any(
        name and all(ch in "-=_~" for ch in name)
        for name in summary.ast.clauses
    )


def test_split_import_alias_recovery(tmp_path):
    write_module(tmp_path, "Lib", "module Lib where\n")
    path = write_module(
        tmp_path,
        "SplitAlias",
        """module SplitAlias where

import Lib as L
""",
    )
    summary = Checker(tmp_path).parse_summary(path)
    assert summary.imports.get("L") == "Lib"


def test_record_where_layout_has_no_syntax_false_positive(tmp_path):
    path = write_module(
        tmp_path,
        "RecordWhere",
        """module RecordWhere where

record R : Set₁ where
  constructor r
  field
    A : Set
    x : A
""",
    )
    diagnostics = Checker(tmp_path).check(path)
    assert not any(d.code == "TSAGDA000" for d in diagnostics)
    summary = Checker(tmp_path).parse_summary(path)
    assert set(summary.ast.records["R"].fields) == {"A", "x"}



def test_arbitrary_function_heads_do_not_make_equality_type_mismatch(tmp_path):
    path = write_module(
        tmp_path,
        "EqualityHeads",
        """module EqualityHeads where

theorem :
  (x : X) →
  f x ≡ g x
theorem x = refl
""",
    )
    diagnostics = Checker(tmp_path).check(path)
    assert not any(d.code in {"TSAGDA100", "TSAGDA105"} for d in diagnostics)


def test_constructor_heads_from_different_datatypes_are_rigidly_incompatible(tmp_path):
    path = write_module(
        tmp_path,
        "RigidEquality",
        """module RigidEquality where

data A : Set where
  a : A

data B : Set where
  b : B

bad : a ≡ b
bad = refl
""",
    )
    diagnostics = Checker(tmp_path).check(path)
    assert any(d.code in {"TSAGDA075", "TSAGDA100", "TSAGDA105"} for d in diagnostics)


def test_import_exports_include_data_and_constructors(tmp_path):
    write_module(
        tmp_path,
        "ExportLib",
        """module ExportLib where

data D : Set where
  c : D

record R : Set where
  constructor r
  field
    A : Set
""",
    )
    path = write_module(
        tmp_path,
        "ExportUse",
        """module ExportUse where

open import ExportLib using (D; c; R; r; A)
""",
    )
    diagnostics = Checker(tmp_path).check(path)
    assert not any(d.code == "TSAGDA023" for d in diagnostics)



def test_import_exports_include_nested_modules(tmp_path):
    write_module(
        tmp_path,
        "NestedExport",
        """module NestedExport where

module SSP where
  x : Set
  x = Set
""",
    )
    path = write_module(
        tmp_path,
        "NestedUse",
        """module NestedUse where

open import NestedExport using (SSP)
""",
    )
    diagnostics = Checker(tmp_path).check(path)
    assert not any(d.code == "TSAGDA023" for d in diagnostics)



def test_untyped_forall_binders_count_individually(tmp_path):
    from agda_preflight.shapes import (
        PiShape,
        UnknownShape,
        explicit_arity,
        shape_from_node,
    )

    path = write_module(
        tmp_path,
        "UntypedForall",
        """module UntypedForall where

f :
  ∀ p q →
  p ≢ q →
  Result p q
f p q neq = rhs
""",
    )
    summary = Checker(tmp_path).parse_summary(path)
    signature = summary.ast.signatures["f"]
    shape = shape_from_node(summary.ast.source_bytes, signature.type_node)

    assert isinstance(shape, PiShape)
    assert explicit_arity(shape) == 3
    assert isinstance(shape.domains[0].head, UnknownShape)
    assert isinstance(shape.domains[1].head, UnknownShape)

    diagnostics = Checker(tmp_path).check(path)
    assert not any(d.code in {"TSAGDA045", "TSAGDA110"} for d in diagnostics)


def test_untyped_implicit_forall_group_counts_each_binder(tmp_path):
    from agda_preflight.shapes import PiShape, all_arity, explicit_arity, shape_from_node

    path = write_module(
        tmp_path,
        "ImplicitForall",
        """module ImplicitForall where

f :
  ∀ {m Δ q} →
  (x : X m Δ q) →
  Result x
f {m} {Δ} {q} x = rhs
""",
    )
    summary = Checker(tmp_path).parse_summary(path)
    signature = summary.ast.signatures["f"]
    shape = shape_from_node(summary.ast.source_bytes, signature.type_node)

    assert isinstance(shape, PiShape)
    assert all_arity(shape) == 4
    assert explicit_arity(shape) == 1


def test_base369_style_forall_clause_arity_is_not_flagged(tmp_path):
    path = write_module(
        tmp_path,
        "Base369Style",
        """module Base369Style where

triXor-assoc :
  ∀ a b c →
  triXor a (triXor b c) ≡ triXor (triXor a b) c
triXor-assoc tri-low tri-low tri-low = refl
""",
    )

    diagnostics = Checker(tmp_path).check(path)
    assert not any(d.code in {"TSAGDA045", "TSAGDA110"} for d in diagnostics)



def test_with_continuation_clauses_inherit_owning_function(tmp_path):
    path = write_module(
        tmp_path,
        "WithOwner",
        """module WithOwner where

gcdTable : A → A → Nat
gcdTable p q with p ≟ q
... | yes _ = one
... | no _  = zero
""",
    )

    summary = Checker(tmp_path).parse_summary(path)

    assert "gcdTable" in summary.ast.clauses
    assert len(summary.ast.clauses["gcdTable"]) == 3
    assert "yes" not in summary.ast.clauses
    assert "no" not in summary.ast.clauses

    diagnostics = Checker(tmp_path).check(path)
    assert not any(d.code == "TSAGDA010" for d in diagnostics)


def test_where_local_helpers_do_not_enter_top_level_clause_table(tmp_path):
    path = write_module(
        tmp_path,
        "WhereLocal",
        """module WhereLocal where

outer : A → A
outer x = helper x
  where
    helper : A → A
    helper y = y
""",
    )

    summary = Checker(tmp_path).parse_summary(path)

    assert "outer" in summary.ast.clauses
    assert "helper" not in summary.ast.clauses
    assert "helper" not in summary.ast.signatures



def test_public_reexport_is_visible_to_downstream_using(tmp_path):
    write_module(
        tmp_path,
        "BaseExport",
        """module BaseExport where

x : Set
x = Set
""",
    )
    write_module(
        tmp_path,
        "MiddleExport",
        """module MiddleExport where

open import BaseExport public using (x)
""",
    )
    path = write_module(
        tmp_path,
        "UseExport",
        """module UseExport where

open import MiddleExport using (x)
""",
    )

    diagnostics = Checker(tmp_path).check(path)
    assert not any(d.code in {"TSAGDA021", "TSAGDA023"} for d in diagnostics)


def test_public_reexport_renaming_changes_visible_name(tmp_path):
    write_module(
        tmp_path,
        "RenameBase",
        """module RenameBase where

x : Set
x = Set
""",
    )
    write_module(
        tmp_path,
        "RenameMiddle",
        """module RenameMiddle where

open import RenameBase public renaming (x to y)
""",
    )
    path = write_module(
        tmp_path,
        "RenameUse",
        """module RenameUse where

open import RenameMiddle using (y)
""",
    )

    checker = Checker(tmp_path)
    summary = checker.parse_summary(tmp_path / "RenameMiddle.agda")
    assert "y" in checker.exported_names(summary)

    diagnostics = checker.check(path)
    assert not any(d.code in {"TSAGDA021", "TSAGDA023"} for d in diagnostics)



def test_nested_record_literal_uses_parent_field_record_type(tmp_path):
    path = write_module(
        tmp_path,
        "NestedRecordTarget",
        """module NestedRecordTarget where

record Inner : Set where
  field
    innerA : Set
    innerB : Set

record Outer : Set where
  field
    outerA : Set
    inner : Inner

mk : Outer
mk =
  record
    { outerA = Set
    ; inner =
        record
          { innerA = Set
          ; innerB = Set
          }
    }
""",
    )

    diagnostics = Checker(tmp_path).check(path)
    assert not any(d.code in {"TSAGDA060", "TSAGDA062"} for d in diagnostics)


def test_nested_record_literal_unknown_parent_type_is_not_guessed(tmp_path):
    path = write_module(
        tmp_path,
        "NestedRecordUnknown",
        """module NestedRecordUnknown where

record Outer : Set₁ where
  field
    Payload : Set
    payload : Payload

mk : Outer
mk =
  record
    { Payload = Set
    ; payload =
        record
          { arbitraryField = Set
          }
    }
""",
    )

    diagnostics = Checker(tmp_path).check(path)
    assert not any(
        d.code in {"TSAGDA060", "TSAGDA062"}
        and d.line >= 12
        for d in diagnostics
    )
