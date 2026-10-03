from pathlib import Path

from agda_preflight.cli import main


def write_module(root: Path, module: str, source: str) -> Path:
    path = root.joinpath(*module.split(".")).with_suffix(".agda")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(source, encoding="utf-8")
    return path


def noisy_module(tmp_path: Path) -> Path:
    return write_module(
        tmp_path,
        "Noisy",
        """module Noisy where

missing : Set

hole : Set
hole = ?
""",
    )


def test_errors_only_hides_warnings_but_keeps_errors(tmp_path, capsys):
    path = noisy_module(tmp_path)

    status = main([str(path), "--root", str(tmp_path), "--errors-only"])
    output = capsys.readouterr().out

    assert status == 1
    assert "TSAGDA012" in output
    assert "TSAGDA008" not in output
    assert ": warning:" not in output


def test_errors_only_filters_json_payload(tmp_path, capsys):
    path = noisy_module(tmp_path)

    status = main(
        [str(path), "--root", str(tmp_path), "--json", "--errors-only"]
    )
    output = capsys.readouterr().out

    assert status == 1
    assert '"TSAGDA012"' in output
    assert '"TSAGDA008"' not in output
    assert '"severity": "warning"' not in output


def test_quiet_suppresses_human_output_but_preserves_exit_status(tmp_path, capsys):
    path = noisy_module(tmp_path)

    status = main([str(path), "--root", str(tmp_path), "--quiet"])
    output = capsys.readouterr().out

    assert status == 1
    assert output == ""


def test_quiet_success_is_silent(tmp_path, capsys):
    path = write_module(tmp_path, "Clean", "module Clean where\n")

    status = main([str(path), "--root", str(tmp_path), "--quiet"])
    output = capsys.readouterr().out

    assert status == 0
    assert output == ""
