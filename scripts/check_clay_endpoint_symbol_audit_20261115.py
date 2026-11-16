#!/usr/bin/env python3
"""Fail-closed rollup-only exact-symbol and phase-ledger preflight.

Authoritative input:
  Docs/roadmaps/ClaySixFrontierABCExactGates20261114.json
  .six_endpoint_exact_symbol_audit_20261115.symbol_index

Run from Agda Clay #1499 checkout:
  python3 scripts/check_clay_endpoint_symbol_audit_20261115.py
  python3 scripts/check_clay_endpoint_symbol_audit_20261115.py --lean-root ../dashi_lean4

This is a SOURCE-STRUCTURE audit, not Agda/Lean kernel acceptance.
It never changes files or silently promotes terminal gates.
"""
from __future__ import annotations
import argparse
from collections import Counter
from pathlib import Path
import json
import re
import subprocess
import sys

AUDIT = "six_endpoint_exact_symbol_audit_20261115"
SIX_CLAY = "clay_six_millennium_endpoints_20261115"
LEDGER = "Docs/roadmaps/ClaySixFrontierABCExactGates20261114.json"
SIX_CANONICAL_IDS = ("NS", "YM", "RH", "BSD", "HODGE", "PNP")
NEW_RESEARCH_GATE_IDS = (
    "R1", "R2", "R3", "R4",
    "S1", "S2", "S3", "S4", "S5", "S6",
    "H1", "H2", "H3",
)
ROOT = Path(__file__).resolve().parents[1]
SIMPLE = re.compile(r"^[A-Za-z_][A-Za-z_0-9.]*$")
STATUS = {
    "SOURCE_TERM_UNCHECKED", "SOURCE_CANDIDATE_UNCHECKED",
    "CONDITIONAL_RECORD", "CONDITIONAL_COMPILER", "EXPLICIT_OPEN_FLAG",
    "OPEN_ENUM_CONSTRUCTOR", "TARGET_NAME_ONLY", "TARGET_TYPE_UNINHABITED",
    "COST_MODEL_COVERAGE_CONSTRUCTED", "KNOWN_NEGATIVE_CONTROL",
    "REFUTED_UNIVERSAL_AUX", "CONDITIONAL_EQUIVALENCE", "SOURCE_MODULE_REUSED",
}

def tracked_source(root: Path) -> list[Path]:
    try:
        result = subprocess.run(
            ["git", "-C", str(root), "ls-files", "-z", "--", "*.agda", "*.lean"],
            capture_output=True, check=True,
        )
    except (OSError, subprocess.CalledProcessError) as exc:
        raise RuntimeError(f"Need original checked-out Git tree: {exc}") from exc
    return [root / p.decode() for p in result.stdout.split(b"\0") if p]

def git_blob_sha(root: Path, filename: str) -> str:
    """Hash exact original file bytes using Git's content-addressed format."""
    path = root / filename
    result = subprocess.run(
        ["git", "-C", str(root), "hash-object", "--", str(path)],
        capture_output=True, text=True, check=True,
    )
    return result.stdout.strip()

def declaration(body: str, name: str) -> bool:
    target = name.split(".")[-1]
    # Agda declarations/record fields and Lean theorem/def/structure names.
    expr = re.compile(
        rf"^\s*(?:(?:theorem|lemma|def|noncomputable\s+def|record|data|"
        rf"structure|abbrev|instance)\s+)?{re.escape(target)}\s*(?::|=|where\b)",
        re.M,
    )
    return bool(expr.search(body))

def main() -> int:
    arg = argparse.ArgumentParser()
    arg.add_argument("--lean-root", type=Path, help="Optional exact native Lean #108 checkout")
    arg.add_argument("--strict", action="store_true",
                     help="Fail if source declarations are missing or target-only names gained bodies")
    opts = arg.parse_args()
    ledger = ROOT / LEDGER
    if not ledger.is_file():
        print(f"BLOCKED: missing canonical {ledger}", file=sys.stderr)
        return 2
    data = json.loads(ledger.read_text())
    audit = data[AUDIT]
    index = audit["symbol_index"]
    if len(index) < 100 or len(audit["gates"]) != 15:
        print("BLOCKED: canonical ledger truncated", file=sys.stderr)
        return 2
    roots = {"agda": ROOT}
    if opts.lean_root:
        roots["lean"] = opts.lean_root.resolve()
    files = {k: tracked_source(v) for k, v in roots.items()}
    cache: dict[Path, str] = {}
    def body(path: Path) -> str:
        if path not in cache:
            cache[path] = path.read_text(encoding="utf-8", errors="replace")
        return cache[path]
    counts = Counter()
    problems = []
    # Audit the actual content-addressed source receipts, not filenames alone.
    evidence = audit.get("p0_source_evidence", {})
    original = evidence.get("observed", {})
    lean_receipts = evidence.get("lean_sources", {})
    if len(original) != 47 or len(lean_receipts) != 3:
        problems.append("P0_RECEIPT_TRUNCATED: expected 47 Agda and 3 Lean owners")
    # User-authorized mathematical/source gate decisions, not native kernels.
    # C1/C2: real Fourier; B1: negative refutation; E2: same-original N21
    # signed-word NP via independent actual bit verifier; F1: standard TM P.
    # E2 does not claim E1's priority/FRACTRAN physical clock or native InNP.
    manifest = audit.get("gates", [])
    completed = [g["id"] for g in manifest if g.get("closed", False)]
    active = [g["id"] for g in manifest if not g.get("closed", False)]
    if (len(manifest) != 15
            or audit.get("active_gate_count") != 9
            or audit.get("active_gate_ids") != active
            or audit.get("completed_gate_ids") != ["P0", "B1", "C1", "C2", "E2", "F1"]
            or completed != ["P0", "B1", "C1", "C2", "E2", "F1"]):
        problems.append("PHASE_GATE_COUNT_MISMATCH: 6/15 user-protocol decisions, 9 active")
    for gate_id, script in [
        ("C1", "check_clay_c1_r71_r74_sympy_bridge_20261115.py"),
        ("C2", "check_clay_c2_r853_selected_rate_sympy_20261115.py"),
    ]:
        gate = next((g for g in manifest if g["id"] == gate_id), None)
        if (gate is None
                or gate.get("status") != "CLOSED_MATHEMATICAL_PYTHON_SYMPY"
                or gate.get("native_agda_theorem_inhabited") is not False
                or gate.get("native_kernel_proof_receipt") is not False
                or gate.get("physical_R408_time_packet_constructed") is not False
                or not (ROOT / "scripts" / script).is_file()):
            problems.append(f"{gate_id}_PYTHON_CLOSURE_PROTOCOL_OR_NATIVE_DEBT_MISSING")
    b1 = next((g for g in manifest if g["id"] == "B1"), None)
    if (b1 is None
            or b1.get("status") != "CLOSED_REFUTED_UNRESTRICTED_REAL_FOURIER"
            or b1.get("closure_kind") != "NEGATIVE_ROUTE_REFUTATION_NOT_POSITIVE_PHYSICAL_SIGNED_PAYMENT"
            or b1.get("original_positive_B1_target_proved") is not False
            or b1.get("unrestricted_R820_R825_nonnegative_payment_possible") is not False
            or b1.get("native_agda_theorem_inhabited") is not False
            or b1.get("physical_R408_time_packet_constructed") is not False
            or not (ROOT / "scripts/check_clay_b1_r820_r825_real_signed_payment_nogo_20261115.py").is_file()):
        problems.append("B1_UNRESTRICTED_SIGNED_PAYMENT_NEGATIVE_DECISION_MISSING_OR_FALSELY_POSITIVE")
    b2 = next((g for g in manifest if g["id"] == "B2"), None)
    if (b2 is None or b2.get("closed") is not False
            or b2.get("dependency_20261115_B1_unrestricted_no_go", {}).get(
                "cannot_use_original_R821_unrestricted_signed_payment_as_true") is not True):
        problems.append("B2_NOT_LEFT_OPEN_AFTER_B1_UNRESTRICTED_NO_GO")
    e2 = next((g for g in manifest if g["id"] == "E2"), None)
    if (e2 is None
            or e2.get("status") != "CLOSED_MATHEMATICAL_ORIGINAL_N21_BITWORD_NP"
            or e2.get("original_signed_weighted_maxcut_word_language_mathematically_in_NP") is not True
            or e2.get("native_PR_InNP_term_constructed") is not False
            or e2.get("native_PR_PolynomialCostModel_BitWord_constructed") is not False
            or e2.get("native_agda_theorem_inhabited") is not False
            or e2.get("native_kernel_proof_receipt") is not False
            or e2.get("E1_specific_selected_priority_FRACTRAN_machine_clock_proved") is not False
            or not (ROOT / "scripts/check_clay_e2_n21_original_bit_np_20261115.py").is_file()):
        problems.append("E2_ORIGINAL_N21_NP_MATHEMATICAL_SOURCE_OR_NATIVE_DEBT_MISSING")
    for parent in ("E0", "E1"):
        gate = next((g for g in manifest if g["id"] == parent), None)
        if gate is None or gate.get("closed") is not False:
            problems.append(f"{parent}_FALSELY_PROMOTED_FROM_E2_DIFFERENT_BIT_TM")
    f1 = next((g for g in manifest if g["id"] == "F1"), None)
    if (f1 is None
            or f1.get("status") != "CLOSED_MATHEMATICAL_STANDARD_TM_PYTHON_PROTOCOL"
            or f1.get("mathematical_standard_P_model_identification") is not True
            or f1.get("native_HaltingStandardCostClosure_record_inhabited") is not False
            or f1.get("full_native_machine_phase_compiler_source_written") is not False
            or f1.get("native_agda_theorem_inhabited") is not False
            or f1.get("native_kernel_proof_receipt") is not False
            or not (ROOT / "scripts/check_clay_f1_standard_tm_model_20261115.py").is_file()):
        problems.append("F1_MATHEMATICAL_MODEL_CLOSURE_OR_NATIVE_FORMAL_DEBT_MISSING")
    for downstream in ("F2", "F3"):
        gate = next((g for g in manifest if g["id"] == downstream), None)
        if gate is None or gate.get("closed") is not False:
            problems.append(f"{downstream}_FALSELY_CLOSED_BY_F1_COST_MODEL_ALONE")
    c2 = next((g for g in manifest if g["id"] == "C2"), None)
    if c2 is None or c2.get("original_typed_R408_R853_real_field_transport_closed") is not False:
        problems.append("C2_ORIGINAL_R408_TYPED_PHYSICAL_WELD_FALSIFIED_OR_MISSING")

    # The historical 15 A-F workstreams are not the six Clay problems.
    # The expanded scope MUST retain every original gate unchanged and
    # separately record RH, BSD and Hodge with exact universal endpoints.
    scope = data.get(SIX_CLAY, {})
    six = scope.get("six_clay_problems", [])
    added = scope.get("newly_added_exact_gates", [])
    original_ids = [g["id"] for g in manifest]
    new_ids = [g.get("id") for g in added]
    expanded = original_ids + new_ids
    if ([e.get("id") for e in six] != list(SIX_CANONICAL_IDS)
            or len(six) != 6
            or scope.get("clay_endpoint_theorems_proved_count") != 0
            or any(e.get("terminal_proved") is not False for e in six)):
        problems.append("SIX_CLAY_ENDPOINTS_MISSING_OR_FALSELY_PROMOTED")
    if (new_ids != list(NEW_RESEARCH_GATE_IDS)
            or len(set(expanded)) != 28
            or scope.get("all_gate_ids") != expanded
            or scope.get("new_gate_count") != 13
            or scope.get("expanded_portfolio_gate_total") != 28):
        problems.append("SIX_CLAY_NEW_RH_BSD_HODGE_GATE_MANIFEST_INVALID")
    if (scope.get("legacy_gate_total") != 15
            or scope.get("legacy_source_or_math_decisions_settled") != 6
            or scope.get("legacy_active_gates") != 9
            or scope.get("expanded_portfolio_decisions_settled") != 13
            or scope.get("expanded_portfolio_active_gates") != 15
            or scope.get("expanded_portfolio_decision_ids") != completed + ["R1", "S1", "S2", "S3", "S4", "H1", "H2"]
            or scope.get("expanded_portfolio_active_ids") != active +
                [g.get("id") for g in added if g.get("settled") is not True]
            or scope.get("legacy_completed_ids") != completed
            or scope.get("legacy_active_ids") != active):
        problems.append("SIX_CLAY_LEGACY_OR_EXPANDED_GATE_COUNTS_MISMATCH")
    # Only S4 selected-curve analytic L positivity is classical-closed;
    # this cannot promote S3 arithmetic MW rank or S5/S6 BSD.
    s4 = next((g for g in added if g.get("id") == "S4"), None)
    if (s4 is None
            or s4.get("settled") is not True
            or s4.get("status") !=
                "CLOSED_CLASSICAL_ORIGINAL_SELECTED_E32_ISOGENY_ETA_MELLIN_POSITIVE"
            or s4.get("mathematical_positive_L_E_one") is not True
            or s4.get("mathematical_all_n_modular_form_coeff_equality") is not True
            or s4.get("native_kernel_acceptance") is not False
            or s4.get("native_elliptic_L_to_form_identification_typechecked") is not False
            or s4.get("original_endpoint_proved") is not False
            or s4.get("S3_original_MW_rank_zero_proved") is not False
            or s4.get("S5_original_all_primary_sha_full_coefficient_proved") is not False
            or not (ROOT / "Docs/roadmaps/ClayBSDOriginalLevel32S4ClassicalClosure20261116.md").is_file()
            or not (ROOT / "scripts/check_clay_s4_original_level32_classical_20261116.py").is_file()):
        problems.append("BSD_S4_CLASSICAL_SELECTED_E_NATIVE_OR_UNIVERSAL_FIREWALL_MISSING")
    if any((g.get("settled") is not False or
            g.get("status") != "OPEN" or
            g.get("native_kernel_acceptance") is not False or
            g.get("original_endpoint_proved") is not False)
           for g in added if g.get("id") not in ("R1", "S1", "S2", "S3", "S4", "H1", "H2")):
        problems.append("OTHER_SIX_NEW_RH_BSD_HODGE_GATE_FALSELY_PROVED")
    if scope.get("newly_added_settled_gate_ids") != ["R1", "S1", "S2", "S3", "S4", "H1", "H2"]:
        problems.append("BSD_S4_EXPANDED_DECISION_ID_MISMATCH")
    r1 = next((g for g in added if g.get("id") == "R1"), None)
    if (r1 is None
            or r1.get("settled") is not True
            or r1.get("status") !=
                "CLOSED_CLASSICAL_ACTUAL_COMPLETED_ZETA_ALL_TERM_WEIL_EXPLICIT_FORMULA"
            or r1.get("actual_all_term_weil_explicit_formula_classically_established") is not True
            or r1.get("actual_zeros_not_assumed_on_critical_line") is not True
            or r1.get("weil_positivity_independently_proved") is not False
            or r1.get("dashi_weil_quadratic_identification_proved") is not False
            or r1.get("native_completed_zeta_owner_instantiated") is not False
            or r1.get("native_weil_explicit_formula_instantiated") is not False
            or r1.get("native_kernel_acceptance") is not False
            or r1.get("original_endpoint_proved") is not False
            or not (ROOT / "Docs/roadmaps/ClayRHR1ActualCompletedZetaWeilExplicitFormulaClassicalClosure20261116.md").is_file()
            or not (ROOT / "scripts/check_clay_r1_weil_formula_normalization_20261116.py").is_file()):
        problems.append("RH_R1_ACTUAL_WEIL_FORMULA_CLASSICAL_POSITIVITY_NATIVE_FIREWALL_MISSING")
    s3 = next((g for g in added if g.get("id") == "S3"), None)
    if (s3 is None
            or s3.get("settled") is not True
            or s3.get("status") !=
                "CLOSED_CLASSICAL_ORIGINAL_SEL2_FOUR_SHA2_ZERO_RANK_ZERO"
            or s3.get("actual_global_Selmer_two_cardinality") != 4
            or s3.get("actual_all_place_Selmer_H1_exhaustion_proved") is not True
            or s3.get("selected_Sha2_zero_proved") is not True
            or s3.get("original_selected_MW_rank_zero_classically_proved") is not True
            or s3.get("native_actual_original_Selmer_realization_instantiated") is not False
            or s3.get("native_MW_Stoll_adapter_typechecked") is not False
            or s3.get("native_kernel_acceptance") is not False
            or s3.get("original_endpoint_proved") is not False
            or not (ROOT / "Docs/roadmaps/ClayBSDOriginalS3GlobalSelmerSha2RankZeroClassicalClosure20261116.md").is_file()
            or not (ROOT / "scripts/check_clay_s3_original_selmer_classical_20261116.py").is_file()):
        problems.append("BSD_S3_ORIGINAL_GLOBAL_SELMER_CLASSICAL_NATIVE_FIREWALL_MISSING")
    s1 = next((g for g in added if g.get("id") == "S1"), None)
    if (s1 is None
            or s1.get("settled") is not True
            or s1.get("status") !=
                "CLOSED_CLASSICAL_ACTUAL_Q2_EIGHT_KUMMER_IMAGE_AND_GLOBAL_H1"
            or s1.get("actual_Q2_local_Kummer_image_cardinality") != 8
            or s1.get("actual_Q2_local_image_all_eight_witnesses_distinct") is not True
            or s1.get("local_Kummer_image_8class_exhaustion_proved") is not True
            or s1.get("native_actual_H1_implementation_instantiated") is not False
            or s1.get("native_kernel_acceptance") is not False
            or s1.get("original_endpoint_proved") is not False
            or not (ROOT / "Docs/roadmaps/ClayBSDOriginalS1Q2EightImageClassicalClosure20261116.md").is_file()
            or not (ROOT / "scripts/check_clay_s1_original_q2_eight_image_20261116.py").is_file()):
        problems.append("BSD_S1_ORIGINAL_Q2_EIGHT_CLASSICAL_NATIVE_FIREWALL_MISSING")
    h1 = next((g for g in added if g.get("id") == "H1"), None)
    if (h1 is None
            or h1.get("settled") is not True
            or h1.get("status") !=
                "CLOSED_CLASSICAL_ALL_VARIETY_RATIONAL_HODGE_AND_CYCLE_BACKGROUND"
            or h1.get("mathematical_actual_rational_Hodge_intersection") is not True
            or h1.get("mathematical_actual_cycle_class_map_all_codimensions") is not True
            or h1.get("native_HodgePiece_complex_vector_space_correct") is not False
            or h1.get("native_Q_to_C_extension_of_scalars_implemented") is not False
            or h1.get("H3_original_universal_cycle_surjectivity_proved") is not False
            or h1.get("native_kernel_acceptance") is not False
            or h1.get("original_endpoint_proved") is not False
            or not (ROOT / "Docs/roadmaps/ClayHodgeH1ActualAllVarietyClassicalBackgroundClosure20261116.md").is_file()
            or not (ROOT / "scripts/check_clay_h1_rational_complex_hodge_firewall_20261116.py").is_file()):
        problems.append("HODGE_H1_CLASSICAL_BACKGROUND_NATIVE_COMPLEX_OR_H3_FIREWALL_MISSING")
    h2 = next((g for g in added if g.get("id") == "H2"), None)
    if (h2 is None
            or h2.get("settled") is not True
            or h2.get("status") !=
                "CLOSED_CLASSICAL_LITERAL_CP1_CP1xCP1_RATIONAL_CYCLE_CLASS"
            or h2.get("actual_algebraic_rational_cycle_surjectivity_CP1") is not True
            or h2.get("actual_algebraic_rational_cycle_surjectivity_CP1xCP1") is not True
            or h2.get("native_literal_CP1_geometry_weld_typechecked") is not False
            or h2.get("general_H3_universal_Hodge_proved") is not False
            or h2.get("native_kernel_acceptance") is not False
            or h2.get("original_endpoint_proved") is not False
            or not (ROOT / "Docs/roadmaps/ClayHodgeH2LiteralCP1GeometryClassicalClosure20261116.md").is_file()
            or not (ROOT / "scripts/check_clay_h2_cp1_geometric_classical_20261116.py").is_file()):
        problems.append("HODGE_H2_CLASSICAL_CP1_GEOMETRY_NATIVE_OR_UNIVERSAL_FIREWALL_MISSING")
    for leaf in ("H3",):
        hg = next((g for g in added if g.get("id") == leaf), None)
        if hg is None or hg.get("settled") is not False:
            problems.append("HODGE_"+leaf+"_FALSELY_PROMOTED_FROM_CP1_SPECIAL_CASE")
    s2 = next((g for g in added if g.get("id") == "S2"), None)
    if (s2 is None
            or s2.get("settled") is not True
            or s2.get("status") !=
                "CLOSED_CLASSICAL_ACTUAL_GLOBAL_LOCAL_KUMMER_SHA_TWO_EXACT_SEQUENCE"
            or s2.get("mathematical_actual_E_valued_Sha_kernel") is not True
            or s2.get("mathematical_all_place_local_Kummer_H1_exact") is not True
            or s2.get("mathematical_Selmer_to_classical_Sha_two_surjective") is not True
            or s2.get("native_actual_Sha_two_exact_sequence_typechecked") is not False
            or s2.get("mathematical_original_rank_zero_proved") is not False
            or s2.get("mathematical_universal_BSD_proved") is not False
            or s2.get("native_kernel_acceptance") is not False
            or s2.get("original_endpoint_proved") is not False
            or not (ROOT / "Docs/roadmaps/ClayBSDOriginalS2ActualKummerShaClassicalClosure20261116.md").is_file()
            or not (ROOT / "scripts/check_clay_s2_actual_kummer_sha_classical_20261116.py").is_file()):
        problems.append("BSD_S2_ACTUAL_CLASSICAL_SHA_KUMMER_NATIVE_OR_UNIVERSAL_FIREWALL_MISSING")
    for leaf in ("S1","S3","S5","S6"):
        g = next((g for g in added if g.get("id") == leaf), None)
        if g is None or g.get("settled") is not False:
            problems.append("BSD_"+leaf+"_FALSELY_PROMOTED_FROM_S4_ANALYTIC_POSITIVITY")
    for endpoint in six:
        owned = endpoint.get("legacy_gates", []) + endpoint.get("new_gates", [])
        if (not endpoint.get("terminal_gate_ids") or
                any(gid not in expanded for gid in owned) or
                any(gid not in expanded for gid in endpoint["terminal_gate_ids"])):
            problems.append(f"SIX_CLAY_ENDPOINT_OWNER_OR_TERMINAL_INVALID: {endpoint.get('id')}")
    if not (ROOT / scope.get("source_of_truth_doc", "__missing__")).is_file():
        problems.append("SIX_CLAY_CANONICAL_SIX_PROBLEM_ROADMAP_MISSING")
    for g in added:
        if not g.get("exact_target_terms") or not g.get("original_owner_paths"):
            problems.append(f"SIX_CLAY_TARGET_OR_OWNER_MISSING {g.get('id')}")
            continue
        for path_string in g["original_owner_paths"]:
            if path_string.endswith(".lean"):
                if "lean" not in roots:
                    counts["SIX_CLAY_LEAN_ROOT_NOT_PROVIDED"] += 1
                    continue
                owner_root = roots["lean"]
            else:
                owner_root = ROOT
            if not (owner_root / path_string).is_file():
                problems.append(f"SIX_CLAY_ORIGINAL_OWNER_MISSING {g['id']}: {path_string}")
    for owner, receipt in original.items():
        if (ROOT / owner).is_file():
            actual = git_blob_sha(ROOT, owner)
            if actual != receipt["blob"]:
                problems.append(f"P0_AGDA_OWNER_CHANGED {owner}: {actual} != {receipt['blob']}")
        else:
            problems.append(f"P0_AGDA_OWNER_MISSING {owner}")
    if "lean" in roots:
        for owner, receipt in lean_receipts.items():
            if (roots["lean"] / owner).is_file():
                actual = git_blob_sha(roots["lean"], owner)
                if actual != receipt["blob"]:
                    problems.append(f"P0_LEAN_OWNER_CHANGED {owner}: {actual} != {receipt['blob']}")
            else:
                problems.append(f"P0_LEAN_OWNER_MISSING {owner}")
    # Every historical donor exact blob identity has an independently fetched
    # SHA in the ledger; ensure the local Clay copy retains that exact content.
    p0 = next((g for g in audit["gates"] if g["id"] == "P0"), None)
    if p0 is None or not p0.get("closed"):
        problems.append("P0_NOT_CLOSED_OR_MISSING")
    else:
        for pair in p0["acceptance_evidence"]["donor_blob_matches"]:
            filename = pair["path"]
            if (ROOT / filename).is_file():
                actual = git_blob_sha(ROOT, filename)
                if actual != pair["donor_blob"]:
                    problems.append(f"P0_DONOR_BLOB_CHANGED {filename}")
            else:
                problems.append(f"P0_DONOR_BLOB_MISSING {filename}")
    for entry in index:
        name = entry["term"]
        kind = entry["classification"]
        lane = entry["lane"]
        owner = entry["owner"]
        root = roots.get(entry["repo"])
        counts[f"{lane}:{kind}"] += 1
        if kind not in STATUS:
            problems.append(f"UNKNOWN_CLASS {lane}: {name} ({kind})")
            continue
        if root is None:
            counts["LEAN_CHECKOUT_NOT_PROVIDED"] += 1
            continue
        path = root / owner
        if not path.is_file():
            problems.append(f"OWNER_MISSING {lane}: {owner} for {name}")
            continue
        if kind == "SOURCE_MODULE_REUSED":
            continue  # Module/source file verified above, not an identically named binder.
        if not SIMPLE.fullmatch(name):
            continue  # Explicit natural-language and compound gate labels.
        leaf = name.split(".")[-1]
        actual = declaration(body(path), name)
        # A target may be superseded by an existing declaration in some other
        # original source owner; do not pretend default-branch search is enough.
        if kind == "TARGET_NAME_ONLY":
            matches = [str(p.relative_to(root)) for p in files[entry["repo"]]
                       if declaration(body(p), name)]
            if matches:
                problems.append(
                    f"RECLASSIFY_TARGET {lane}: {name} now declared in {matches[:4]}"
                )
            continue
        if kind in {
            "SOURCE_TERM_UNCHECKED", "SOURCE_CANDIDATE_UNCHECKED",
            "COST_MODEL_COVERAGE_CONSTRUCTED", "EXPLICIT_OPEN_FLAG",
        } and not actual:
            # It can be a sourced import rather than a local binder; inspect,
            # don't automatically call it disproved.
            problems.append(f"VERIFY_DECLARATION {lane}: {name} in {owner}")
        if kind == "EXPLICIT_OPEN_FLAG" and actual:
            flagged = re.search(rf"^\s*{re.escape(leaf)}\s*=\s*false\b", body(path), re.M)
            if not flagged:
                problems.append(f"FLAG_CHANGED {lane}: {name} no longer '= false'")
    print(json.dumps({
        "schema": "six-endpoint-source-audit-run-v1",
        "repo": str(ROOT), "symbol_entries": len(index),
        "phase_gates": len(audit["gates"]),
        "clay_problem_count": len(data.get(SIX_CLAY, {}).get("six_clay_problems", [])),
        "expanded_portfolio_gates": len(audit["gates"]) + len(data.get(SIX_CLAY, {}).get("newly_added_exact_gates", [])),
        "original_clay_endpoints_proved": data.get(SIX_CLAY, {}).get("clay_endpoint_theorems_proved_count"),
        "classification_counts": counts,
        "problems": problems,
        "claim": "SOURCE_STRUCTURE_ONLY_NOT_KERNEL_CERTIFICATION",
    }, indent=2, sort_keys=True, default=dict))
    if problems and opts.strict:
        return 1
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
