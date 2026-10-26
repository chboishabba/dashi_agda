#!/usr/bin/env python3
"""Quality-conditioned finite design audit. Stdlib only; no external experiments."""
from __future__ import annotations
import json
from dataclasses import dataclass

@dataclass(frozen=True)
class Trial:
    name: str
    val_loss: float
    wall_seconds: float
    gpu_count: int
    gpu_type: str
    tokens: int
    source: str
    full_search_accounted: bool = False

    def qualifies(self, threshold: float = 4.2) -> bool:
        return self.val_loss <= threshold

def comparable(a: Trial, b: Trial) -> bool:
    return (a.tokens == b.tokens and a.gpu_count == b.gpu_count
            and a.gpu_type == b.gpu_type
            and a.full_search_accounted and b.full_search_accounted)

def quality_dominates(a: Trial, b: Trial) -> bool:
    return (a.val_loss <= b.val_loss
            and a.wall_seconds <= b.wall_seconds
            and (a.val_loss < b.val_loss or a.wall_seconds < b.wall_seconds))

def admitted_dominance(a: Trial, b: Trial) -> bool:
    return comparable(a, b) and quality_dominates(a, b)

def main() -> None:
    baseline = Trial("Dust/Adam initial", 4.167, 1.76*3600, 8, "H100", 10_000_000,
        "https://github.com/qlabs-eng/noise", False)
    speedrun = Trial("Noise claimed record", 4.2, 1.6, 8, "H100", 10_000_000,
        "https://github.com/qlabs-eng/noise", False)
    ratio = baseline.wall_seconds / speedrun.wall_seconds
    assert ratio == 3960
    assert baseline.qualifies() and speedrun.qualifies()
    assert not admitted_dominance(speedrun, baseline)
    assert not admitted_dominance(baseline, speedrun)
    print(json.dumps({
      "source": baseline.source, "reported_speed_ratio": ratio,
      "baseline_threshold_pass": baseline.qualifies(),
      "speedrun_threshold_pass": speedrun.qualifies(),
      "quality_adjusted_dominance_verified": False,
      "reason": "Record is threshold-oriented; full search costs and independent receipts are not supplied by this fixture",
      "scope": "source-reported numeric fixture, not an independent reproduction"
    }, indent=2))

if __name__ == "__main__":
    main()
