#!/usr/bin/env python3
"""Probe whether selected historical imports are needed by Agda elaboration.

The probe is isolated in a disposable source copy.  It removes only the
selected import lines, invokes the repository-sanctioned Agda checker, and
records the result.  A passing probe is evidence for that exact consumer
variant only; it is not a declaration mapping or deletion authorization.
"""

from __future__ import annotations

import argparse
import json
import os
import signal
import subprocess
import tarfile
import tempfile
from collections import defaultdict
from pathlib import Path


def prepare_probe_root(repo_root: Path) -> tuple[tempfile.TemporaryDirectory, Path]:
    """Create one disposable source copy for all variants of one consumer."""
    temp = tempfile.TemporaryDirectory(prefix="dashi-round-probe-")
    probe_root = Path(temp.name) / "repo"
    probe_root.mkdir(parents=True)
    archive = Path(temp.name) / "repo.tar"
    with archive.open("wb") as handle:
        subprocess.run(["git", "archive", "HEAD"], cwd=repo_root,
                       check=True, stdout=handle)
    with tarfile.open(archive) as handle:
        handle.extractall(probe_root)
    subprocess.run([
        "rsync", "-a", "--include=*/", "--include=*.agda",
        "--include=*.lagda", "--exclude=*", f"{repo_root}/", f"{probe_root}/",
    ], check=True, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True)
    diff = subprocess.run(
        ["git", "diff", "--", "*.agda"], cwd=repo_root, check=True,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
    ).stdout
    if diff:
        applied = subprocess.run(["git", "apply", "-"], cwd=probe_root,
                                 input=diff, capture_output=True, text=True)
        if applied.returncode != 0:
            already_present = subprocess.run(
                ["git", "apply", "--reverse", "--check", "-"],
                cwd=probe_root, input=diff, capture_output=True, text=True,
            )
            if already_present.returncode != 0:
                raise subprocess.CalledProcessError(
                    applied.returncode, applied.args,
                    output=applied.stdout, stderr=applied.stderr,
                )
    return temp, probe_root


def run_probe(repo_root: Path, audit: dict, consumer: str, selected_rows: list[dict] | None = None,
              timeout: int = 900, rss_limit: int = 8192,
              prepared_root: Path | None = None) -> dict:
    rows = selected_rows or [row for row in audit["rows"] if row["consumer"] == consumer]
    if not rows:
        raise ValueError(f"no context-audit rows for consumer: {consumer}")
    consumer_path = repo_root / rows[0]["consumer_path"]
    remove_lines = {row["historical_module"]: row["line"] for row in rows}

    temporary = None
    if prepared_root is None:
        temporary, probe_root = prepare_probe_root(repo_root)
    else:
        probe_root = prepared_root
    try:
        target = probe_root / rows[0]["consumer_path"]
        lines = target.read_text(encoding="utf-8").splitlines(keepends=True)
        removed = []
        for number, line in enumerate(lines, 1):
            matched = next((module for module, line_number in remove_lines.items()
                            if number == line_number and module in line), None)
            if matched:
                removed.append(matched)
            else:
                removed.append(None)
        original_text = "".join(lines)
        target.write_text("".join(line for line, marker in zip(lines, removed) if marker is None), encoding="utf-8")

        command = [
            "scripts/run_agda29_parallel_check.sh",
            rows[0]["consumer_path"],
        ]
        process = subprocess.Popen(
            command,
            cwd=probe_root,
            env={**os.environ,
                 "DASHI_NO_TMUX": "1",
                 "AGDA_JOBS": "1",
                 "DASHI_AGDA_RSS_LIMIT_MB": str(rss_limit)},
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            start_new_session=True,
        )
        try:
            stdout, stderr = process.communicate(timeout=timeout)
            returncode = process.returncode
            status = "probe-pass" if returncode == 0 else "probe-fail"
        except subprocess.TimeoutExpired as exc:
            os.killpg(process.pid, signal.SIGTERM)
            stdout, stderr = process.communicate(timeout=30)
            returncode = 124
            status = "probe-timeout"
            stdout = (stdout or "") + (exc.stdout or "")
            stderr = (stderr or "") + (exc.stderr or "")
        result = {
            "consumer": consumer,
            "consumer_path": rows[0]["consumer_path"],
            "removed_historical_modules": [row["historical_module"] for row in rows],
            "removed_line_count": len(rows),
            "command": f"DASHI_NO_TMUX=1 AGDA_JOBS=1 DASHI_AGDA_RSS_LIMIT_MB={rss_limit} " + " ".join(command),
            "returncode": returncode,
            "status": status,
            "authorization": "batch-evidence-only",
            "output_tail": (stdout + stderr)[-6000:],
        }
        target.write_text(original_text, encoding="utf-8")
        return result
    finally:
        if temporary is not None:
            temporary.cleanup()


def adaptive_probe(repo_root: Path, audit: dict, consumer: str, rows: list[dict],
                   timeout: int, max_probes: int, rss_limit: int) -> list[dict]:
    """Probe a consumer in batches, splitting failed batches conservatively.

    A passing batch is evidence only for that exact edited variant.  A failed
    batch is recursively split so one hidden elaboration dependency does not
    hide the other candidates.  The result deliberately does not authorize
    individual import removal.
    """
    queue = [rows]
    receipts: list[dict] = []
    temporary, probe_root = prepare_probe_root(repo_root)
    try:
      while queue and len(receipts) < max_probes:
        batch = queue.pop(0)
        receipt = run_probe(repo_root, audit, consumer, batch, timeout, rss_limit, probe_root)
        receipt["batch_index"] = len(receipts)
        receipts.append(receipt)
        if receipt["status"] == "probe-fail" and len(batch) > 1 and len(receipts) < max_probes:
            midpoint = len(batch) // 2
            queue.insert(0, batch[midpoint:])
            queue.insert(0, batch[:midpoint])
      if queue:
        receipts.append({
            "consumer": consumer,
            "status": "probe-budget-exhausted",
            "authorization": "none",
            "remaining_batch_count": len(queue),
        })
      return receipts
    finally:
      temporary.cleanup()


def write_result(output: Path, result: dict) -> None:
    output.parent.mkdir(parents=True, exist_ok=True)
    temporary = output.with_suffix(output.suffix + ".tmp")
    temporary.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    temporary.replace(output)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("consumer", nargs="?", help="consumer module to probe")
    parser.add_argument("--all", action="store_true", help="probe every audited consumer")
    parser.add_argument("--adaptive", action="store_true",
                        help="split failed consumer batches to isolate context dependencies")
    parser.add_argument("--max-probes", type=int, default=32,
                        help="maximum Agda invocations per consumer in adaptive mode")
    parser.add_argument("--timeout", type=int, default=900)
    parser.add_argument("--rss-limit", type=int, default=8192,
                        help="DASHI_AGDA_RSS_LIMIT_MB passed to the sanctioned wrapper")
    parser.add_argument("--resume", action="store_true",
                        help="resume a prior --all output and skip completed consumers")
    parser.add_argument("--max-consumers", type=int, default=0,
                        help="stop after this many newly processed consumers (0 means all)")
    parser.add_argument("--repo-root", type=Path, default=Path("."))
    parser.add_argument("--audit", type=Path, default=Path(".dashi/round-stranded/ym-context-audit.json"))
    parser.add_argument("--output", type=Path, default=Path(".dashi/round-stranded/ym-context-probe.json"))
    args = parser.parse_args()
    root = args.repo_root.resolve()
    audit = json.loads((root / args.audit).read_text(encoding="utf-8"))
    if args.all and args.consumer:
        parser.error("pass either a consumer or --all, not both")
    if not args.all and not args.consumer:
        parser.error("a consumer or --all is required")
    if args.all:
        grouped: dict[str, list[dict]] = defaultdict(list)
        for row in audit["rows"]:
            grouped[row["consumer"]].append(row)
        output = root / args.output
        prior = {}
        if args.resume and output.is_file():
            existing = json.loads(output.read_text(encoding="utf-8"))
            if existing.get("schema_version") == 2:
                for receipt in existing.get("receipts", []):
                    consumer = receipt.get("consumer")
                    if consumer:
                        prior.setdefault(consumer, []).append(receipt)
        receipts = [receipt for consumer in sorted(prior) for receipt in prior[consumer]]
        processed = 0
        for consumer, rows in sorted(grouped.items()):
            existing_receipts = prior.get(consumer, [])
            if existing_receipts and not any(
                receipt.get("status") == "probe-budget-exhausted"
                for receipt in existing_receipts
            ):
                continue
            if args.max_consumers and processed >= args.max_consumers:
                break
            if existing_receipts:
                receipts = [receipt for receipt in receipts if receipt.get("consumer") != consumer]
            if args.adaptive:
                receipts.extend(adaptive_probe(root, audit, consumer, rows, args.timeout, args.max_probes, args.rss_limit))
            else:
                receipts.append(run_probe(root, audit, consumer, rows, args.timeout, args.rss_limit))
            processed += 1
            write_result(output, {
                "schema_version": 2,
                "purpose": "Agda context probe receipts; batch evidence never authorizes deletion",
                "consumer_count": len(grouped),
                "processed_consumer_count": len({receipt.get("consumer") for receipt in receipts if receipt.get("consumer")}),
                "receipt_count": len(receipts),
                "receipts": receipts,
                "deletion_authorized": False,
            })
        result = {
            "schema_version": 2,
            "purpose": "Agda context probe receipts; batch evidence never authorizes deletion",
            "consumer_count": len(grouped),
            "receipt_count": len(receipts),
            "receipts": receipts,
            "deletion_authorized": False,
        }
    else:
        rows = [row for row in audit["rows"] if row["consumer"] == args.consumer]
        result = {
            "schema_version": 2,
            "purpose": "Agda context probe receipt; batch evidence never authorizes deletion",
            "receipt": run_probe(root, audit, args.consumer, rows, args.timeout, args.rss_limit),
            "deletion_authorized": False,
        }
    output = root / args.output
    write_result(output, result)
    print(json.dumps({
        "consumer_count": result.get("consumer_count", 1),
        "receipt_count": result.get("receipt_count", 1),
        "deletion_authorized": result["deletion_authorized"],
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
