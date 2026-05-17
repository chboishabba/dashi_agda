#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import selectors
import subprocess
import sys
import time
from pathlib import Path
from typing import Any


DEFAULT_DYTURBO = Path("temp-DOWNLOADED/dyturbo/unpacked/bin/dyturbo")
DEFAULT_RUN_DIR = Path("temp-DOWNLOADED/dyturbo/run_cms_smoke")
DEFAULT_DYTPATH = Path("temp-DOWNLOADED/dyturbo/unpacked/share/dyturbo")
DEFAULT_LHAPDF = Path("scripts/data/pdf")

NUMBER = r"[+-]?(?:(?:\d+(?:\.\d*)?)|(?:\.\d+))(?:[eE][+-]?\d+)?"
QT_ROW = re.compile(rf"^\|\s*({NUMBER})\s*-\s*({NUMBER})\s*\|")


PROGRESS_HANDLE = None


def emit(event: str, **fields: Any) -> None:
    payload = {
        "event": event,
        "time_unix": time.time(),
        **fields,
    }
    line = json.dumps(payload, sort_keys=True)
    print(line, flush=True)
    if PROGRESS_HANDLE is not None:
        PROGRESS_HANDLE.write(line + "\n")
        PROGRESS_HANDLE.flush()


def fmt_seconds(seconds: float | None) -> str | None:
    if seconds is None:
        return None
    seconds = max(0.0, seconds)
    if seconds < 90:
        return f"{seconds:.0f}s"
    minutes = seconds / 60.0
    if minutes < 90:
        return f"{minutes:.1f}m"
    return f"{minutes / 60.0:.1f}h"


def count_qt_bins(card_path: Path) -> int | None:
    text = card_path.read_text(encoding="utf-8", errors="ignore")
    match = re.search(r"^\s*qt_bins\s*=\s*\[([^\]]+)\]", text, re.MULTILINE)
    if not match:
        return None
    edges = [part for part in match.group(1).split() if part]
    if len(edges) < 2:
        return None
    return len(edges) - 1


def output_stem(card_path: Path) -> str | None:
    text = card_path.read_text(encoding="utf-8", errors="ignore")
    match = re.search(r"^\s*output_filename\s*=\s*([^#\s]+)", text, re.MULTILINE)
    return match.group(1) if match else None


def find_outputs(run_dir: Path, stem: str | None) -> list[str]:
    if not stem:
        return []
    return sorted(str(path) for path in run_dir.glob(f"{stem}*"))


def sha256_prefix(path: Path) -> str | None:
    if not path.exists():
        return None
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()[:16]


def run(args: argparse.Namespace) -> int:
    global PROGRESS_HANDLE
    run_dir = Path(args.run_dir)
    card_path = Path(args.card)
    if not card_path.is_absolute():
        card_path = run_dir / card_path
    binary = Path(args.dyturbo)
    if not binary.is_absolute():
        binary = Path.cwd() / binary

    total_bins = count_qt_bins(card_path)
    stem = output_stem(card_path)
    started = time.monotonic()
    last_heartbeat = started
    rows_done = 0
    last_line = ""

    env = os.environ.copy()
    env["DYTPATH"] = str(Path(args.dytpath).resolve())
    env["LHAPDF_DATA_PATH"] = str(Path(args.lhapdf_data_path).resolve())

    if args.progress_jsonl:
        progress_path = Path(args.progress_jsonl)
        if not progress_path.is_absolute():
            progress_path = run_dir / progress_path
        progress_path.parent.mkdir(parents=True, exist_ok=True)
        PROGRESS_HANDLE = progress_path.open("a", encoding="utf-8")

    emit(
        "start",
        card=str(card_path),
        dyturbo=str(binary),
        run_dir=str(run_dir),
        total_bins=total_bins,
        output_stem=stem,
        heartbeat_seconds=args.heartbeat_seconds,
        card_sha256_16=sha256_prefix(card_path),
        dyturbo_sha256_16=sha256_prefix(binary),
        progress_jsonl=str(Path(args.progress_jsonl)) if args.progress_jsonl else None,
    )

    try:
        proc = subprocess.Popen(
            [str(binary), str(card_path.relative_to(run_dir) if card_path.is_relative_to(run_dir) else card_path)],
            cwd=run_dir,
            env=env,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
        )
        emit("subprocess", pid=proc.pid)

        assert proc.stdout is not None
        os.set_blocking(proc.stdout.fileno(), False)
        selector = selectors.DefaultSelector()
        selector.register(proc.stdout, selectors.EVENT_READ)
        pending = ""
        while True:
            now = time.monotonic()
            lines: list[str] = []
            events = selector.select(timeout=0.2)
            if events:
                try:
                    chunk = os.read(proc.stdout.fileno(), 8192)
                except BlockingIOError:
                    chunk = b""
                if chunk:
                    pending += chunk.decode(errors="replace")
                    parts = pending.splitlines(keepends=True)
                    pending = ""
                    for part in parts:
                        if part.endswith("\n") or part.endswith("\r"):
                            lines.append(part.rstrip("\r\n"))
                        else:
                            pending = part
                elif proc.poll() is not None:
                    if pending:
                        lines.append(pending)
                        pending = ""
                    break

            for line in lines:
                last_line = line
                if args.echo:
                    print(last_line, flush=True)
                if QT_ROW.search(last_line):
                    rows_done += 1
                    elapsed = now - started
                    fraction = None
                    eta = None
                    if total_bins:
                        fraction = min(rows_done / total_bins, 1.0)
                        eta = elapsed * (1.0 / fraction - 1.0) if fraction > 0 else None
                    emit(
                        "progress",
                        phase="bin_rows",
                        rows_done=rows_done,
                        total_bins=total_bins,
                        fraction=fraction,
                        elapsed_seconds=elapsed,
                        eta_seconds=eta,
                        eta_human=fmt_seconds(eta),
                        last_row=last_line[:240],
                    )
            if not lines and proc.poll() is not None:
                if pending:
                    last_line = pending
                    if args.echo:
                        print(last_line, flush=True)
                    pending = ""
                break

            if now - last_heartbeat >= args.heartbeat_seconds:
                elapsed = now - started
                fraction = rows_done / total_bins if total_bins and rows_done else None
                eta = elapsed * (1.0 / fraction - 1.0) if fraction else None
                emit(
                    "heartbeat",
                    phase="running",
                    pid=proc.pid,
                    rows_done=rows_done,
                    total_bins=total_bins,
                    fraction=fraction,
                    elapsed_seconds=elapsed,
                    eta_seconds=eta,
                    eta_human=fmt_seconds(eta),
                    last_line=last_line[:240],
                    output_candidates=find_outputs(run_dir, stem),
                )
                last_heartbeat = now

        returncode = proc.wait()
        elapsed = time.monotonic() - started
        emit(
            "complete" if returncode == 0 else "failed",
            returncode=returncode,
            elapsed_seconds=elapsed,
            elapsed_human=fmt_seconds(elapsed),
            rows_done=rows_done,
            total_bins=total_bins,
            output_candidates=find_outputs(run_dir, stem),
        )
        return returncode
    finally:
        if PROGRESS_HANDLE is not None:
            PROGRESS_HANDLE.close()
            PROGRESS_HANDLE = None


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Run DYTurbo and emit JSONL progress/heartbeat/ETA events for UI orchestration."
    )
    parser.add_argument("card", help="DYTurbo card path, absolute or relative to --run-dir.")
    parser.add_argument("--dyturbo", default=str(DEFAULT_DYTURBO))
    parser.add_argument("--run-dir", default=str(DEFAULT_RUN_DIR))
    parser.add_argument("--dytpath", default=str(DEFAULT_DYTPATH))
    parser.add_argument("--lhapdf-data-path", default=str(DEFAULT_LHAPDF))
    parser.add_argument("--heartbeat-seconds", type=float, default=30.0)
    parser.add_argument(
        "--progress-jsonl",
        help="Optional progress log path. Relative paths are resolved under --run-dir.",
    )
    parser.add_argument("--echo", action="store_true", help="Also echo DYTurbo stdout lines.")
    return parser.parse_args()


def main() -> int:
    return run(parse_args())


if __name__ == "__main__":
    raise SystemExit(main())
