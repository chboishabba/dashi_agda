#!/usr/bin/env python3
"""Source-text contract across DASHI, SensibLaw and SLR.

Default mode validates DASHI's authored bridge only. Use BOTH explicit
--sensiblaw-root and --slr-root to also check the sibling source trees.
Neither mode runs Agda, cargo, pytest, postgres or judicial review.
"""
from __future__ import annotations

import argparse
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CASE = ROOT / "DASHI/Law/SensibLawWoogarooEPBC8575PleadableGroundsPrecedentCut20261028Exact.agda"
BRIDGE = ROOT / "DASHI/Law/SensibLawWoogarooSLRCasePaymentInterop20261028Exact.agda"
ROLLUP = ROOT / "DASHI/Law/SensibLawWoogarooPreservationEverything.agda"
MEMO = ROOT / "Docs/SaveWoogarooSLRSensibLawCaseInteropMaxCut20261028.md"

GROUNDS = (
    ("adviceGround", "advice-consideration"),
    ("recoveryGround", "recovery-plan"),
    ("actionImpactGround", "incremental-habitat"),
    ("commentsGround", "comment-transmission"),
    ("scopeGround", "approval-scope"),
    ("localPrestartGround", "local-prestart"),
    ("politicalTheory", "improper-influence"),
)

def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--sensiblaw-root", type=Path)
    parser.add_argument("--slr-root", type=Path)
    args = parser.parse_args()
    if (args.sensiblaw_root is None) != (args.slr_root is None):
        parser.error("supply both sibling roots or neither, never only one")
    case, bridge, rollup, memo = (
        p.read_text(encoding="utf-8") for p in (CASE, BRIDGE, ROLLUP, MEMO)
    )
    assert case.count("= case-hypothesis") == 7
    assert bridge.count("= native-matter-interop") == 7
    assert bridge.count("refl refl refl refl") == 7
    assert bridge.count("→ ⊥") == 10
    assert bridge.count("persistedSpanPaid : Bool") == 1
    assert bridge.count("caseWitnessPaid : Bool") == 1
    assert bridge.count("courtDeterminationPaid : Bool") == 1
    assert rollup.count(
        "import DASHI.Law.SensibLawWoogarooSLRCasePaymentInterop20261028Exact"
    ) == 1
    assert "matter:au:epbc:2019-8575:postapproval" in bridge
    assert "woogaroo-case-cut:v0_1" in bridge
    assert "[PR #59]" in memo and "SensibLaw" in memo
    assert "2015" in memo and "Mackay Conservation Group" in memo
    assert "consent" in memo.lower() and "removed before enactment" in memo
    # Scenic may be described in a type-level no-promotion firewall.
    # The actual bridge rows must still target Springview only.
    assert bridge.count('"2019/8575"') == 7
    assert 'matchedEPBCAction : String' in bridge

    for native, cross in GROUNDS:
        assert f"Case.{native}" in bridge, native
        assert f'"candidate-ground:{cross}"' in bridge, cross
    for original in (
        "Merits.s139", "Cumulative.locatedLocalRegionalIntegrationResidual",
        "Counsel.organisationStanding", "File.section95CRecommendation",
        "Condition.condition6aCouncilAcceptance",
    ):
        assert original.split(".")[-1] in case + bridge, original
    assert bridge.count('(just "residual:woogaroo:') == 2
    assert "sourceLocatorOnly" in bridge
    assert "SourceAdmissionCompileEligibleEqualsPaidExactSpan" in bridge
    assert "SLRUnreviewedFixtureEqualsPersistedControversy" in bridge
    assert "StatisticalOrFinancialOverlapEqualsImproperInfluence" in bridge

    if args.sensiblaw_root is None:
        print("PASS: DASHI seven-ground crosswalk + 10 anti-promotions; "
              "SLR/SensibLaw sibling source and runtime NOT checked")
        return

    sensiblaw = (args.sensiblaw_root /
                 "src/sources/woogaroo_case_cut.py").read_text(encoding="utf-8")
    sensiblaw_test = (args.sensiblaw_root /
                     "tests/sources/test_woogaroo_case_cut.py").read_text(encoding="utf-8")
    slr = (args.slr_root /
           "crates/sl-pg-source-store/tests/woogaroo_2019_8575_candidate_controversy.rs").read_text(encoding="utf-8")
    for _, cross in GROUNDS:
        assert f'"{cross}"' in sensiblaw, cross
    assert "SourceAdmissionProfile" in sensiblaw
    assert '"gate": 0' in sensiblaw
    assert '"persisted_revision_paid": False' in sensiblaw
    assert '"exact_span_paid": False' in sensiblaw
    assert '"actual_filing_paid": False' in sensiblaw
    assert "eligible_as_springview_merits_evidence" in sensiblaw_test
    assert "swfg-scenic-letter" in sensiblaw_test
    assert "matter:au:epbc:2019-8575:postapproval" in slr
    for residual in (
        "residual:woogaroo:correct-advice-consideration",
        "residual:woogaroo:habitat-function-vs-retained-width",
    ):
        assert residual in slr, residual
    assert "reviewed_evidence_ref: None" in slr
    assert "MatterEpistemicStatus::Unresolved" in slr
    assert "creates_actual_reopening" in slr
    assert "MatterResponseMode::AdmitConductAddContext" not in slr
    print("PASS: cross-repository case sources align; runtime/tests remain unexecuted")


if __name__ == "__main__":
    main()
