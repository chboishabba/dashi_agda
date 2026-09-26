from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
import time
from typing import IO, Any, Dict, Optional, Tuple

from .apply_edits import EditApplicationError, apply_text_edits
from .source_index import SourceIndex
from .semantic_catalog import SemanticCatalog
from .promotion import CommandPromoter
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
        semantic_catalog: Optional[Path] = None,
        promoter_command: Optional[str] = None,
        promoter_timeout: float = 900.0,
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
        self.semantic_path = (
            semantic_catalog.resolve()
            if semantic_catalog is not None
            else None
        )
        self.semantic = (
            SemanticCatalog(self.semantic_path)
            if self.semantic_path is not None
            and self.semantic_path.exists()
            else None
        )
        self.promoter = (
            CommandPromoter(
                promoter_command,
                root=self.root,
                catalog=self.semantic_path,
                timeout=promoter_timeout,
            )
            if promoter_command is not None
            and self.semantic_path is not None
            else None
        )

    def close(self) -> None:
        if self.semantic is not None:
            self.semantic.close()
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

    def _ensure_semantic_catalog(self) -> None:
        if (
            self.semantic is None
            and self.semantic_path is not None
            and self.semantic_path.exists()
        ):
            self.semantic = SemanticCatalog(self.semantic_path)

    def _refresh_semantic_catalog(self) -> None:
        if self.semantic is not None:
            self.semantic.close()
            self.semantic = None
        self._ensure_semantic_catalog()

    def _semantic_lookup(
        self,
        module_hashes: Dict[str, str],
    ) -> Dict[str, dict]:
        self._ensure_semantic_catalog()
        if self.semantic is None or not module_hashes:
            return {}
        with self.profiler.stage("semantic.catalog_lookup"):
            items = self.semantic.lookup(
                module_hashes,
                module_hashes,
            )
        return {
            module: item.as_dict()
            for module, item in sorted(items.items())
        }

    @staticmethod
    def _semantic_counts(items: Dict[str, dict]) -> dict:
        return {
            "fresh": sum(
                1 for item in items.values()
                if item["freshness"] == "fresh"
            ),
            "stale": sum(
                1 for item in items.values()
                if item["freshness"] == "stale"
            ),
            "unknown": sum(
                1 for item in items.values()
                if item["freshness"] == "unknown"
            ),
        }

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
        semantic = self._semantic_lookup(
            dict(result.source_hashes)
        )
        return {
            "modules": list(result.modules),
            "cache_hit": result.cache_hit,
            "diagnostics": [
                item.as_dict()
                for item in diagnostics
            ],
            "semantic": semantic,
            "semantic_counts": self._semantic_counts(semantic),
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
        semantic = {}
        if diagnostic is not None and self.semantic_path is not None:
            identity = self.index.source_identity(diagnostic.path)
            if identity is not None:
                module_name, source_hash = identity
                semantic = self._semantic_lookup(
                    {module_name: source_hash}
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
            "semantic": semantic,
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

    def semantic_status(self, target: str) -> dict:
        before, started = self._start_request()
        hashes = self.index.closure_source_hashes(Path(target))
        if hashes is None:
            result = self.index.diagnose(Path(target))
            hashes = result.source_hashes
        module_hashes = dict(hashes)
        semantic = self._semantic_lookup(module_hashes)
        counts = self._semantic_counts(semantic)
        return {
            "modules": len(module_hashes),
            "catalog_hits": len(semantic),
            "catalog_misses": max(
                0,
                len(module_hashes) - len(semantic),
            ),
            "fresh": counts["fresh"],
            "stale": counts["stale"],
            "unknown": counts["unknown"],
            "snapshots": semantic,
            "profile": self._finish_request(before, started),
        }

    @staticmethod
    def _output_tail(text: str, limit: int = 8192) -> str:
        return text if len(text) <= limit else text[-limit:]

    def promote(self, target: str) -> dict:
        if self.promoter is None:
            raise ValueError(
                "semantic promotion is not configured; "
                "start the service with --semantic-catalog and --promoter-command"
            )
        if self.semantic_path is None:
            raise ValueError("semantic catalog path is not configured")

        before, started = self._start_request()
        target_path = Path(target)
        if not target_path.is_absolute():
            target_path = self.root / target_path
        target_path = target_path.resolve()

        # Refresh source identity before invoking any external checker.
        result = self.index.diagnose(target_path)
        identity = self.index.source_identity(target_path)
        if identity is None:
            raise ValueError(
                f"target is not indexed as an Agda module: {target_path}"
            )
        module_name, source_hash = identity

        command_result = self.promoter.run(
            path=target_path,
            module=module_name,
        )

        # The external writer may have created or replaced the catalog. Reopen
        # it and prove promotion from the checked-source SHA postcondition.
        self._refresh_semantic_catalog()
        semantic = self._semantic_lookup(
            dict(result.source_hashes)
        )
        target_semantic = semantic.get(module_name)
        freshness = (
            target_semantic["freshness"]
            if target_semantic is not None
            else "unknown"
        )

        if command_result.returncode != 0:
            status = "failed"
        elif freshness == "fresh":
            status = "promoted"
        else:
            status = "unverified"

        counts = self._semantic_counts(semantic)
        receipt = {
            "status": status,
            "module_name": module_name,
            "target_path": str(target_path),
            "source_sha256": source_hash,
            "promoter_returncode": command_result.returncode,
            "promoter_elapsed_ms": round(
                command_result.elapsed_ms,
                3,
            ),
            "semantic_freshness": freshness,
            "semantic_counts": counts,
            "semantic": target_semantic,
            "promoter_receipt": command_result.receipt,
            "stdout_tail": self._output_tail(
                command_result.stdout
            ),
            "stderr_tail": self._output_tail(
                command_result.stderr
            ),
        }
        receipt_id = self.index.record_promotion(receipt)
        receipt["receipt_id"] = receipt_id
        receipt["profile"] = self._finish_request(before, started)
        return receipt

    def promotion_history(
        self,
        module_name: Optional[str] = None,
        limit: int = 20,
    ) -> dict:
        before, started = self._start_request()
        receipts = self.index.promotion_history(
            module_name=module_name,
            limit=limit,
        )
        return {
            "receipts": receipts,
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
        if method == "semantic_status":
            return self.semantic_status(**params)
        if method == "promote":
            return self.promote(**params)
        if method == "promotion_history":
            return self.promotion_history(**params)
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
    parser.add_argument(
        "--semantic-catalog",
        type=Path,
        help="optional read-only agda2lean semantic catalog",
    )
    parser.add_argument(
        "--promoter-command",
        help=(
            "explicit semantic promotion command; supports {file}, {module}, "
            "{root}, {catalog}, and {receipt} placeholders"
        ),
    )
    parser.add_argument(
        "--promoter-timeout",
        type=float,
        default=900.0,
        help="promotion subprocess timeout in seconds (default: 900)",
    )
    args = parser.parse_args(argv)

    with DashiAgdaService(
        args.root,
        args.index,
        jobs=args.jobs,
        semantic_catalog=args.semantic_catalog,
        promoter_command=args.promoter_command,
        promoter_timeout=args.promoter_timeout,
    ) as service:
        serve_streams(
            service,
            sys.stdin,
            sys.stdout,
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
