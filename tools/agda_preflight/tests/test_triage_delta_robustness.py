from pathlib import Path

from agda_preflight.checker import Diagnostic
from agda_preflight.triage_delta import render_delta
from agda_preflight.triage_render import build_triage


def report(tmp_path):
    diagnostic = Diagnostic(
        "TSAGDA204",
        "Exact module contains unresolved proof placeholder",
        tmp_path / "DASHI" / "Foo.agda",
        10,
        1,
        severity="error",
    )
    return build_triage([diagnostic], tmp_path)


def test_delta_accepts_non_object_previous_snapshot(tmp_path):
    output = render_delta([], report(tmp_path))
    assert "Δ since previous run" in output


def test_delta_treats_nonnumeric_previous_count_as_zero(tmp_path):
    previous = {
        "fingerprint": "old",
        "root_causes": [
            {
                "signature": "old-signature",
                "path": "DASHI/Foo.agda",
                "kind": "placeholder",
                "label": "unresolved proof placeholder",
                "codes": "TSAGDA204",
                "count": "not-a-number",
            }
        ],
    }
    output = render_delta(previous, report(tmp_path))
    assert "Δ since previous run" in output
    assert "fingerprint:" in output
