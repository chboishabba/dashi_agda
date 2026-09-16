from __future__ import annotations

from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
CHECKER = ROOT / "scripts" / "check_monster_3b_five_orbit_d4_n3b_screen.sh"
WORKFLOW = ROOT / ".github" / "workflows" / "monster-3b-actual-kernel-character-round4.yml"


def test_d4_n3b_screen_has_dedicated_checker():
    assert CHECKER.exists(), "expected dedicated D4/N3B screen checker"
    text = CHECKER.read_text()
    assert "monster_3b_five_orbit_d4_n3b_screen.g" in text
    assert "test_monster_3b_five_orbit_d4_n3b_screen.py" in text


def test_existing_monster3b_workflow_executes_and_uploads_screen_receipt():
    text = WORKFLOW.read_text()
    assert "check_monster_3b_five_orbit_d4_n3b_screen.sh" in text
    assert "build/monster_3b_five_orbit_d4_n3b_screen.json" in text
