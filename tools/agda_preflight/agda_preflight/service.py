from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
import time
from typing import IO, Any, Dict, Optional, Tuple

from .apply_edits import EditApplicationError, apply_text_edits
from .source_index import SourceIndex
from .timing import Profiler, TimingSnapshot


def _snapshot_delta(
    before: TimingSnapshot,
    after: TimingSnapshot,
    total_ns: int,
) -> dict:
    stage_names = set(before.stages_ns) | set(after.stages_ns)
    count_names = set(before.counts) | set(after.counts)
    return {
        "request_total_ms": round(total_ns / 1_000_000.0, 3),
        "stages_ms": {
            name: round(
                (
                    after.stages_ns.get(name, 0)
                    - before.stages_ns.get(name, 0)
                )
                / 1_000_000.0,
                3,
            )
            for name in sorted(stage_names)
            if after.stages_ns.get(name, 0)
            != before.stages_ns.get(name, 0)
        },
        "counts": {
            name: (
                after.counts.get(name, 0)
                - before.counts.get(name, 0)
            )
            for name in sorted(count_names)
            if after.counts.get(name, 0)
            != before.counts.get(name, 0)
        },
    }


class DashiAgdaService:
    """Long-lived incremental analysis service over one source-index DB."""

    def __init__(
        self,
        root: Path,
        index_path: Path,
        *,
        jobs: int = 0,
    ) -> None:
        self.root = root.resolve()
        self.profiler = Profiler()
        self.index = SourceIndex(
            self.root,
            index_path,
            profiler=self.profiler,
            jobs=jobs,
        )
        self.jobs = jobs

    def close(self) -> None:
        self.index.close()

    def __enter__(self) -> "DashiAgdaService":
        return self

    def __exit__(self, exc_type, exc, tb) -> None:
        self.close()

    def _start_request(self) -> Tuple[TimingSnapshot, int]:
        self.index.begin_request()
        return self.profiler.snapshot(), time.perf_counter_ns()

    def _finish_request(
        self,
        before: TimingSnapshot,
        started_ns: int,
    ) -> dict:
        return _snapshot_delta(
            before,
            self.profiler.snapshot(),
            time.perf_counter_ns() - started_ns,
        )

    def diagnose(
        self,
        target: str,
        *,
        errors_only: bool = False,
    ) -> dict:
        before, started = self._start_request()
        result = self.index.diagnose(Path(target))
        diagnostics = result.diagnostics
        if errors_only:
            diagnostics = [
                item
                for item in diagnostics
                if item.severity == "error"
            ]
        return {
            "modules": list(result.modules),
            "cache_hit": result.cache_hit,
            "diagnostics": [
                item.as_dict()
                for item in diagnostics
            ],
            "profile": self._finish_request(before, started),
        }

    def next_error(
        self,
        target: str,
        *,
        require_fix: bool = False,
    ) -> dict:
        before, started = self._start_request()
        diagnostic = self.index.next_diagnostic(
            Path(target),
            require_fix=require_fix,
        )
        return {
            "status": (
                "diagnostic"
                if diagnostic is not None
                else "clean"
            ),
            "diagnostic": (
                diagnostic.as_dict()
                if diagnostic is not None
                else None
            ),
            "profile": self._finish_request(before, started),
        }

    def apply_fix(
        self,
        target: str,
        diagnostic_id: str,
        *,
        fix_index: int = 0,
        allow_likely: bool = False,
    ) -> dict:
        before, started = self._start_request()
        target_path = Path(target)

        diagnostic = self.index.find_cached_diagnostic(
            target_path,
            diagnostic_id,
        )
        if diagnostic is None:
            result = self.index.diagnose(target_path)
            diagnostic = next(
                (
                    item
                    for item in result.diagnostics
                    if item.diagnostic_id == diagnostic_id
                ),
                None,
            )
        if diagnostic is None:
            raise ValueError(
                "diagnostic ID is not present in the current source-index result"
            )
        if fix_index < 0 or fix_index >= len(diagnostic.fixes):
            raise ValueError(
                f"diagnostic has {len(diagnostic.fixes)} fix(es); "
                f"fix index {fix_index} is out of range"
            )

        fix = diagnostic.fixes[fix_index]
        if fix.applicability == "speculative":
            raise ValueError(
                "speculative fixes cannot be machine-applied"
            )
        if (
            fix.applicability == "likely"
            and not allow_likely
        ):
            raise ValueError(
                "likely fixes require allow_likely=true"
            )
        if not fix.edits:
            raise ValueError(
                "selected fix has no exact machine-applicable edits"
            )

        try:
            changed = apply_text_edits(fix.edits)
        except EditApplicationError as error:
            raise ValueError(str(error)) from error

        # The edit happened during this request, so clear request-local parsed
        # state once more before verifying the changed module.
        self.index.begin_request()
        after = self.index.diagnose(diagnostic.path)
        resolved = all(
            item.diagnostic_id != diagnostic_id
            for item in after.diagnostics
            if item.path.resolve() == diagnostic.path.resolve()
        )

        return {
            "diagnostic_id": diagnostic_id,
            "fix": fix.as_dict(),
            "changed_files": [
                str(path)
                for path in changed
            ],
            "resolved": resolved,
            "profile": self._finish_request(before, started),
        }

    def cache_status(self) -> dict:
        before, started = self._start_request()
        result = self.index.cache_stats()
        result["profile"] = self._finish_request(
            before,
            started,
        )
        return result

    def dispatch(
        self,
        method: str,
        params: Optional[Dict[str, Any]] = None,
    ) -> dict:
        params = dict(params or {})
        if method == "diagnose":
            return self.diagnose(**params)
        if method == "next_error":
            return self.next_error(**params)
        if method == "apply_fix":
            return self.apply_fix(**params)
        if method == "cache_status":
            return self.cache_status()
        if method == "ping":
            return {"status": "ok"}
        raise ValueError(f"unknown service method: {method}")


def serve_streams(
    service: DashiAgdaService,
    input_stream: IO[str],
    output_stream: IO[str],
) -> None:
    for raw_line in input_stream:
        line = raw_line.strip()
        if not line:
            continue

        request_id = None
        try:
            request = json.loads(line)
            if not isinstance(request, dict):
                raise ValueError("request must be a JSON object")
            request_id = request.get("id")
            method = request.get("method")
            if not isinstance(method, str) or not method:
                raise ValueError("request method must be a non-empty string")

            if method == "shutdown":
                response = {
                    "id": request_id,
                    "ok": True,
                    "result": {"status": "shutdown"},
                }
                output_stream.write(
                    json.dumps(
                        response,
                        sort_keys=True,
                        separators=(",", ":"),
                    )
                    + "\n"
                )
                output_stream.flush()
                return

            params = request.get("params", {})
            if params is None:
                params = {}
            if not isinstance(params, dict):
                raise ValueError("request params must be a JSON object")

            response = {
                "id": request_id,
                "ok": True,
                "result": service.dispatch(method, params),
            }
        except Exception as error:
            response = {
                "id": request_id,
                "ok": False,
                "error": {
                    "type": type(error).__name__,
                    "message": str(error),
                },
            }

        output_stream.write(
            json.dumps(
                response,
                sort_keys=True,
                separators=(",", ":"),
            )
            + "\n"
        )
        output_stream.flush()


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(
        prog="dashi-agda-server",
        description=(
            "Long-lived JSONL service for incremental Agda source diagnostics"
        ),
    )
    parser.add_argument(
        "--root",
        type=Path,
        default=Path.cwd(),
        help="repository root (default: current directory)",
    )
    parser.add_argument(
        "--index",
        type=Path,
        default=Path(".cache/agda_preflight/source-index.sqlite3"),
        help="persistent source-index database",
    )
    parser.add_argument(
        "--jobs",
        type=int,
        default=0,
        help="cold-bootstrap workers; 0 = auto",
    )
    args = parser.parse_args(argv)

    with DashiAgdaService(
        args.root,
        args.index,
        jobs=args.jobs,
    ) as service:
        serve_streams(
            service,
            sys.stdin,
            sys.stdout,
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
