"""Synthetic original-PNAS motion QC regression; not actual participant motion data."""
from pathlib import Path
import importlib.util
import pytest

PATH = Path(__file__).resolve().parents[1] / "scripts/derive_dmt_original_motion_cohort.py"
spec = importlib.util.spec_from_file_location("dmt_original_motion", PATH)
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)


def example():
    people = {s: {"dmt_fd": [0.0] * 840} for s in module.SOURCE_PSEUDONYMS}
    for s in ("S01", "S02", "S03", "S06"):
        people[s]["dmt_fd"][240:289] = [0.5] * 49
    for s in ("S07", "S08", "S09"):
        people[s]["dmt_fd"][0:169] = [0.5] * 169
    return {
        "source": "doi:10.1073/pnas.2218949120",
        "tr_seconds": 2.0,
        "bolus_start_tr": 240,
        "author_or_processor_qc_receipt": "SYNTHETIC TEST ONLY",
        "participants": people,
    }


def test_original_motion_groups_are_separate_consumers():
    outcome = module.derive_motion_cohorts(example())
    assert len(outcome["static_n16"]) == 16
    assert len(outcome["dynamic_n13"]) == 13
    assert "S01" not in outcome["static_n16"]
    assert "S07" in outcome["static_n16"]
    assert "S07" not in outcome["dynamic_n13"]
    assert outcome["independent_source_verified"] is False


def test_strictly_greater_than_twenty_percent():
    fd = [0.0] * 840
    fd[240:288] = [0.5] * 48
    assert module.excluded(fd, 240, 480)["exclude"] is False
    fd[288] = 0.5
    assert module.excluded(fd, 240, 480)["exclude"] is True


def test_nonfinite_and_missing_motion_are_blocked():
    missing = example()
    missing["participants"].pop("S25")
    with pytest.raises(ValueError, match="twenty"):
        module.derive_motion_cohorts(missing)
    corrupt = example()
    corrupt["participants"]["S25"]["dmt_fd"][300] = float("nan")
    with pytest.raises(ValueError, match="Nonfinite"):
        module.derive_motion_cohorts(corrupt)


def test_does_not_force_original_cohort_by_posthoc_relaxing_cutoffs():
    unexpected = example()
    unexpected["participants"]["S10"]["dmt_fd"][0:169] = [0.5] * 169
    with pytest.raises(ValueError, match="did not reproduce"):
        module.derive_motion_cohorts(unexpected)


def test_same_count_foreign_pseudonyms_are_not_source_admitted():
    payload = example()
    payload["participants"]["S04"] = payload["participants"].pop("S25")
    assert len(payload["participants"]) == 20
    with pytest.raises(ValueError, match="author-listed"):
        module.derive_motion_cohorts(payload)
