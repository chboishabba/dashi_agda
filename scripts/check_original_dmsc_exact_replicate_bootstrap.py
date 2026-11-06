#!/usr/bin/env python3
"""Exact finite bootstrap of the two original dmsC RNA9 assay readouts.

Enumerates all 3^3 * 3^3 = 729 ordered resampling outcomes. This is a
nonparametric descriptive bootstrap conditional on the three observed values
per genotype, not a calibrated CI for organismal phenotype or causality.
"""
from __future__ import annotations

import itertools
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OWNER = ROOT / "DASHI/Biology/Physical/OriginalDmscTwoGenotypeMeasuredExact.agda"
SOURCE_GIT_BLOB = "151cd87272cbdd6bcc2b1e70bdfd2a4ea2933d2c"
OBSERVATIONS = {
    "AAAAAAAAA": (256, 769, 664),
    "AAAAAAAAC": (389, 908, 695),
}


def main() -> None:
    text = OWNER.read_text(encoding="utf-8")
    assert SOURCE_GIT_BLOB in text
    assert "originalAAAA = threeReplicateMeasuredMean 256 769 664 563 refl" in text
    assert "originalAAAC = threeReplicateMeasuredMean 389 908 695 664 refl" in text
    before = OBSERVATIONS["AAAAAAAAA"]
    after = OBSERVATIONS["AAAAAAAAC"]
    assert sum(before) == 3 * 563 and sum(after) == 3 * 664

    # All ordered with-replacement resamples of size three in each group,
    # expressed as numerators / 3 to retain exact integer arithmetic.
    difference_numerators = sorted(
        sum(b) - sum(a)
        for a in itertools.product(before, repeat=3)
        for b in itertools.product(after, repeat=3)
    )
    assert len(difference_numerators) == 729
    # Nearest-rank empirical percentiles; 19th and 711th of 729 samples.
    lower = difference_numerators[18] / 3
    upper = difference_numerators[710] / 3
    assert (lower, upper) == (-243.0, 445.0)
    assert difference_numerators[0] == -1140
    assert difference_numerators[-1] == 1956

    cross_pairs = sorted(b - a for a in before for b in after)
    assert cross_pairs == [-380, -275, -74, 31, 133, 139, 244, 439, 652]
    nonpositive = sum(value <= 0 for value in difference_numerators)
    assert nonpositive == 231

    print(json.dumps({
        "result": "passed",
        "study_source_blob": SOURCE_GIT_BLOB,
        "genotype_pair": list(OBSERVATIONS),
        "observed_means_thousandths": [563, 664],
        "observed_difference_thousandths": 101,
        "exhaustive_bootstrap_resamples": 729,
        "bootstrap_percentile_95_nearest_rank_thousandths": [lower, upper],
        "nonpositive_resampled_differences": nonpositive,
        "nonpositive_fraction": f"{nonpositive}/729",
        "all_cross_replicate_differences_thousandths": cross_pairs,
        "interpretation": "interval crosses zero; no source-backed equality or difference significance conclusion",
        "claims_excluded": [
            "independent biological replication", "physical kinetic parameter",
            "developmental attractor", "causal SNP effect"
        ],
    }, indent=2))


if __name__ == "__main__":
    main()
