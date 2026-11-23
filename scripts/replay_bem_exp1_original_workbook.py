#!/usr/bin/env python3
"""Source-exact Bem Experiment 1 replay from original participant workbook.

Usage: python scripts/replay_bem_exp1_original_workbook.py path/to/exp1.xlsx

Reads XLSX via artifact_tool. Does NOT upload/share participant data.
Primary statistic: independent participant-level one-sample t vs 50%,
one-sided. Trial-aggregate binomial analysis is explicitly secondary.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import numpy as np
from scipy import stats
from artifact_tool import Blob, SpreadsheetFile


HEADERS = [
    "Session", "Date", "StartTime", "Session.Length", "Participant.Sex",
    "Participant.Age", "ExpSex", "Erotic.Hits.PC",
    "Control.Hits.PC", "Stimulus.Seeking",
]


def one_sample_greater(x):
    result = stats.ttest_1samp(x, 50)
    return {
        "participant_count": len(x),
        "mean_percent": float(np.mean(x)),
        "t": float(result.statistic),
        "df": len(x) - 1,
        "one_sided_p": float(
            result.pvalue / 2 if result.statistic > 0
            else 1 - result.pvalue / 2
        ),
    }


def replay(path: Path) -> dict:
    wb = SpreadsheetFile.import_xlsx(Blob.load(str(path)))
    rows = wb.worksheets.get_item_at(0).get_range("A1:J101").values
    assert rows[0] == HEADERS, (rows[0], HEADERS)
    records = rows[1:]
    assert len(records) == 100
    assert [r[0] for r in records] == list(range(1, 101))
    assert all(len(r) == 10 and all(cell is not None for cell in r)
               for r in records)

    erotic = np.asarray([r[7] for r in records], float)
    control = np.asarray([r[8] for r in records], float)
    seeking = np.asarray([r[9] for r in records], float)
    trials = np.asarray([12] * 40 + [18] * 60)
    successes = np.rint(erotic * trials / 100).astype(int)
    assert np.max(np.abs(erotic * trials / 100 - successes)) < 1e-9
    assert int(successes[:40].sum()) == 261
    assert int(successes[40:].sum()) == 565

    primary = one_sample_greater(erotic)
    high = seeking > 2.5
    assert high.sum() == 42
    paired = stats.ttest_rel(erotic, control)
    correlation = stats.pearsonr(erotic, seeking)
    first, last = erotic[:40], erotic[40:]

    output = {
        "file_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
        "rows": len(records),
        "primary_2011_erotic_participant_t": primary,
        "control_participant_t": one_sample_greater(control),
        "source_defined_high_seeking_gt_2_5": one_sample_greater(erotic[high]),
        "low_seeking_le_2_5": one_sample_greater(erotic[~high]),
        "stimulus_seeking_correlation": {
            "r": float(correlation.statistic),
            "one_sided_p": float(correlation.pvalue / 2),
        },
        "paired_erotic_minus_control": {
            "t": float(paired.statistic),
            "one_sided_p": float(paired.pvalue / 2),
        },
        "first_40_phase": one_sample_greater(first),
        "last_60_phase": one_sample_greater(last),
        "two_sided_welch_phase_difference_p":
            float(stats.ttest_ind(first, last, equal_var=False).pvalue),
        "high_vs_low_welch_difference_p":
            float(stats.ttest_ind(erotic[high], erotic[~high],
                                  equal_var=False).pvalue),
        "source_trial_reconstruction": {
            "first_40_erotic_trials": 480,
            "last_60_erotic_trials": 1080,
            "successes": int(successes.sum()),
            "trials": int(trials.sum()),
            "pooled_rate_percent": 100 * float(successes.sum() / trials.sum()),
            "one_sided_binomial_p": float(
                stats.binomtest(int(successes.sum()), int(trials.sum()),
                                .5, alternative="greater").pvalue),
            "later_publication_828_successes_does_not_match_workbook": True,
        },
        "scope": "No original trial target-placement or RNG event trace. "
                 "No original preregistration decisions; phase/subgroup "
                 "comparisons are exploratory, not proof of p-hacking. "
                 "A one-sample participant test is NOT a pooled trial binomial.",
    }
    assert round(primary["mean_percent"], 1) == 53.1
    assert round(primary["t"], 2) == 2.51
    assert round(output["source_defined_high_seeking_gt_2_5"]["t"], 2) == 4.57
    assert output["source_trial_reconstruction"]["successes"] == 826
    assert output["source_trial_reconstruction"]["trials"] == 1560
    return output


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("xlsx", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = replay(args.xlsx)
    rendered = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(rendered, encoding="utf8")
    print(rendered)
