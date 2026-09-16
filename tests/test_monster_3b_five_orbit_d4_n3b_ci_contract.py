from __future__ import annotations

from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
CHECKER = ROOT / "scripts" / "check_monster_3b_five_orbit_d4_n3b_screen.sh"
SCREEN = ROOT / "scripts" / "monster_3b_five_orbit_d4_n3b_screen.g"
WORKFLOW = ROOT / ".github" / "workflows" / "monster-3b-actual-kernel-character-round4.yml"
EXECUTION_BRANCH = "agent/monster369-d4-nineorbit-kernel-character-exec"
SUMMARY_SCRIPT = "monster_3b_five_orbit_d4_n3b_receipt_summary.py"
SUMMARY_ARTIFACT = "build/monster_3b_five_orbit_d4_n3b_summary.json"


def test_d4_n3b_screen_has_dedicated_checker():
    assert CHECKER.exists(), "expected dedicated D4/N3B screen checker"
    text = CHECKER.read_text()
    assert "monster_3b_five_orbit_d4_n3b_screen.g" in text
    assert "test_monster_3b_five_orbit_d4_n3b_screen.py" in text


def test_screen_reuses_all_known_good_mn3b_group_construction_fallbacks():
    text = SCREEN.read_text()
    assert "AtlasGroup(groupName)" in text
    assert "GroupInfoForCharacterTable(mn3b)" in text
    assert "GroupForGroupInfo(groupInfo)" in text


def test_checker_classifies_raw_receipt_into_fail_locating_summary():
    text = CHECKER.read_text()
    assert SUMMARY_SCRIPT in text
    assert SUMMARY_ARTIFACT in text


def test_existing_monster3b_workflow_executes_and_uploads_screen_receipt():
    text = WORKFLOW.read_text()
    assert "check_monster_3b_five_orbit_d4_n3b_screen.sh" in text
    assert "build/monster_3b_five_orbit_d4_n3b_screen.json" in text
    assert SUMMARY_ARTIFACT in text


def test_execution_branch_push_deterministically_triggers_existing_gap_workflow():
    text = WORKFLOW.read_text()
    assert EXECUTION_BRANCH in text
