from __future__ import annotations

import importlib.util
import json
import sys
from pathlib import Path
from typing import Any, Iterable

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
STEM = "ns_sprint136_hou_luo_symmetric_source_sign"
SCRIPT = REPO_ROOT / "scripts" / f"{STEM}.py"


def load_sprint136_module() -> Any:
    if not SCRIPT.is_file():
        pytest.skip(f"missing Sprint 136 script: {SCRIPT.relative_to(REPO_ROOT)}")

    spec = importlib.util.spec_from_file_location(STEM, SCRIPT)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[STEM] = module
    spec.loader.exec_module(module)
    return module


def run_sprint136(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> tuple[list[Any], str, Path]:
    module = load_sprint136_module()
    assert hasattr(module, "main"), "Sprint 136 script must expose main"

    out_dir = tmp_path / STEM
    argv = ["--repo-root", str(REPO_ROOT), "--out-dir", str(out_dir)]
    monkeypatch.chdir(REPO_ROOT)
    monkeypatch.setattr(sys, "argv", [str(SCRIPT), *argv])

    try:
        result = module.main(argv)
    except TypeError:
        result = module.main()
    except SystemExit as exc:
        result = exc.code

    text = collect_artifact_text(out_dir)
    assert result in (None, 0), text
    assert out_dir.is_dir(), text

    json_paths = sorted(out_dir.glob("*.json"))
    md_paths = sorted(out_dir.glob("*.md"))
    assert json_paths, text
    assert md_paths, text
    assert all(path.stat().st_size > 0 for path in json_paths + md_paths)

    payloads = [json.loads(path.read_text(encoding="utf-8")) for path in json_paths]
    return payloads, text, out_dir


def collect_artifact_text(out_dir: Path) -> str:
    if not out_dir.exists():
        return ""
    paths = sorted(
        path
        for path in out_dir.glob("*")
        if path.suffix.lower() in {".json", ".csv", ".md", ".txt"}
    )
    return "\n".join(path.read_text(encoding="utf-8", errors="replace") for path in paths)


def walk(value: Any) -> Iterable[Any]:
    yield value
    if isinstance(value, dict):
        for child in value.values():
            yield from walk(child)
    elif isinstance(value, list):
        for child in value:
            yield from walk(child)


def norm(value: Any) -> str:
    return "".join(char for char in str(value).lower() if char.isalnum())


def combined_text(*values: Any) -> str:
    return "\n".join(json.dumps(value, sort_keys=True, default=str) for value in values)


def bool_values_for_key(payloads: list[Any], key_name: str) -> list[bool]:
    wanted = norm(key_name)
    found: list[bool] = []
    for item in walk(payloads):
        if not isinstance(item, dict):
            continue
        for key, value in item.items():
            if norm(key) == wanted and isinstance(value, bool):
                found.append(value)
    return found


def row_mentions(payloads: list[Any], *needles: str) -> bool:
    wanted = tuple(norm(needle) for needle in needles)
    for item in walk(payloads):
        if isinstance(item, dict):
            text = norm(json.dumps(item, sort_keys=True, default=str))
            if all(needle in text for needle in wanted):
                return True
    return False


def test_sprint136_writes_json_summary_and_report(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    payloads, text, out_dir = run_sprint136(tmp_path, monkeypatch)

    assert payloads, text
    assert sorted(out_dir.glob("*.md")), text


def test_sprint136_symmetric_summary_keeps_log_loss_source_lower_bound_false(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    payloads, text, _out_dir = run_sprint136(tmp_path, monkeypatch)

    values = bool_values_for_key(payloads, "LogLossSourceLowerBound")
    assert values, text
    assert all(value is False for value in values), combined_text(payloads) + "\n" + text
    assert row_mentions(payloads, "symmetric", "LogLossSourceLowerBound", "false")


def test_sprint136_records_axial_monotonicity_required_but_open(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    payloads, text, _out_dir = run_sprint136(tmp_path, monkeypatch)

    assert row_mentions(payloads, "axial", "monotonicity", "required"), text
    assert row_mentions(payloads, "axial", "monotonicity", "open"), text


def test_sprint136_records_source_nonpositive_as_conditional(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    payloads, text, _out_dir = run_sprint136(tmp_path, monkeypatch)

    assert row_mentions(payloads, "source", "nonpositive", "conditional"), text


def test_sprint136_does_not_solve_or_promote_clay_ns(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    payloads, text, _out_dir = run_sprint136(tmp_path, monkeypatch)

    full_clay_values = bool_values_for_key(payloads, "full_clay_ns_solved")
    promoted_values = bool_values_for_key(payloads, "clayNavierStokesPromoted")
    assert full_clay_values, text
    assert promoted_values, text
    assert all(value is False for value in full_clay_values)
    assert all(value is False for value in promoted_values)
