#!/usr/bin/env python3
from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import os
import queue
import re
import signal
import subprocess
import sys
import threading
import time
from collections import deque
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Set, Tuple


ROOT_DIR = Path(__file__).resolve().parent.parent
DEFAULT_METADATA = ROOT_DIR / ".cache" / "closure_hygiene_metadata.tsv"
HEAVY_AGGREGATORS = {
    "DASHI/Everything.agda",
    "DASHI/Physics/Closure/PhysicsClosureValidationSummary.agda",
    "DASHI/Physics/Closure/ShiftContractObservableTransportPrimeCompatibilityProfileInstance.agda",
    "DASHI/Physics/Closure/ShiftObservableSignaturePressureConsumer.agda",
    "DASHI/Physics/DashiDynamicsShiftInstance.agda",
    "DASHI/Physics/Closure/CanonicalAbstractGaugeMatterInstance.agda",
    "DASHI/Physics/Closure/CanonicalGaugeMatterStrengtheningTheorem.agda",
    "DASHI/Physics/Closure/KnownLimitsFullMatterGaugeTheorem.agda",
    "DASHI/Physics/Closure/AtomicPhotonuclearContactGateTheorem.agda",
    "DASHI/Physics/Closure/CanonicalP2KeyScheduleBridgeObstruction.agda",
    "DASHI/Physics/Closure/CanonicalScheduleIndependentNaturalChargeNextIngredientGap.agda",
}
ALIAS_TO_KEY = {
    "01": "module:DASHI/Physics/Closure/CanonicalStageCTheoremBundle.agda",
    "02": "module:DASHI/Everything.agda",
    "03": "audit:canonical_path_audit",
    "04": "audit:placeholder_postulate_audit",
    "05": "audit:closure_status_pointers",
}
STAGE_ORDER = ["01", "02", "03", "04", "05"]
IMPORT_RE = re.compile(r"^(?:open import|import)\s+([A-Za-z0-9_.]+)", re.MULTILINE)


@dataclass
class Task:
    key: str
    kind: str
    label: str
    artifact: Path
    command: List[str]
    deps: Set[str] = field(default_factory=set)
    learned_class: str = "fast"
    fingerprint: str = ""
    selected: bool = False


@dataclass
class MetadataRow:
    label: str
    learned_class: str
    fingerprint: str
    rc: int
    duration_secs: int
    timestamp: str


@dataclass
class TaskResult:
    key: str
    rc: int
    duration_secs: int


class Runner:
    def __init__(self, args: argparse.Namespace) -> None:
        self.args = args
        self.root = ROOT_DIR
        self.out_dir = Path(args.out_dir) if args.out_dir else self.root / "artifacts" / f"closure_hygiene_{time.strftime('%Y%m%d_%H%M%S')}"
        self.out_dir.mkdir(parents=True, exist_ok=True)
        self.metadata_file = Path(args.metadata_file)
        if args.cache and self.metadata_file.parent != Path("."):
            self.metadata_file.parent.mkdir(parents=True, exist_ok=True)

        self.ts = time.strftime("%Y%m%d_%H%M%S")
        self.agda_bin = args.agda_bin
        self.metadata: Dict[str, MetadataRow] = self.load_metadata()
        self.tasks: Dict[str, Task] = {}
        self.task_keys: List[str] = []
        self.reverse_deps: Dict[str, Set[str]] = {}
        self.pending_status: Dict[str, int] = {}
        self.pending_duration: Dict[str, int] = {}
        self.pending_skipped: Set[str] = set()
        self.console_lock = threading.Lock()
        self.metadata_lock = threading.Lock()
        self.proc_lock = threading.Lock()
        self.active_processes: Dict[str, subprocess.Popen[str]] = {}
        self.stop_requested = False
        self.executor: Optional[concurrent.futures.ThreadPoolExecutor] = None
        self.common_salt = self.compute_common_salt()
        self._install_signal_handlers()

    def _install_signal_handlers(self) -> None:
        def handler(signum: int, _frame) -> None:
            if self.stop_requested:
                return
            self.stop_requested = True
            self._print("[interrupt] stopping launches, draining completed tasks, terminating running children")
            with self.proc_lock:
                procs = list(self.active_processes.values())
            for proc in procs:
                try:
                    os.killpg(proc.pid, signal.SIGTERM)
                except ProcessLookupError:
                    continue
                except Exception:
                    try:
                        proc.terminate()
                    except Exception:
                        pass

        signal.signal(signal.SIGINT, handler)
        signal.signal(signal.SIGTERM, handler)

    def _print(self, message: str) -> None:
        with self.console_lock:
            print(message, flush=True)

    def load_metadata(self) -> Dict[str, MetadataRow]:
        rows: Dict[str, MetadataRow] = {}
        if not self.args.cache or not self.metadata_file.exists():
            return rows
        for line in self.metadata_file.read_text(encoding="utf-8").splitlines():
            parts = line.split("\t")
            if len(parts) != 7:
                continue
            key, label, learned_class, fingerprint, rc, duration, timestamp = parts
            rows[key] = MetadataRow(
                label=label,
                learned_class=learned_class,
                fingerprint=fingerprint,
                rc=int(rc),
                duration_secs=int(duration),
                timestamp=timestamp,
            )
        return rows

    def save_metadata(self) -> None:
        if not self.args.cache:
            return
        with self.metadata_lock:
            tmp = self.metadata_file.with_suffix(self.metadata_file.suffix + ".tmp")
            keys = sorted(set(self.metadata) | set(self.tasks))
            with tmp.open("w", encoding="utf-8") as fh:
                for key in keys:
                    row = self.metadata.get(key)
                    task = self.tasks.get(key)
                    if row is None:
                        if task is None:
                            continue
                        row = MetadataRow(
                            label=task.label,
                            learned_class=task.learned_class,
                            fingerprint=task.fingerprint,
                            rc=999,
                            duration_secs=999999,
                            timestamp=self.ts,
                        )
                    fh.write(
                        "\t".join(
                            [
                                key,
                                row.label,
                                row.learned_class,
                                row.fingerprint,
                                str(row.rc),
                                str(row.duration_secs),
                                row.timestamp,
                            ]
                        )
                        + "\n"
                    )
            tmp.replace(self.metadata_file)

    def update_metadata_for_result(self, task: Task, rc: int, duration_secs: int) -> None:
        self.metadata[task.key] = MetadataRow(
            label=task.label,
            learned_class=task.learned_class,
            fingerprint=task.fingerprint,
            rc=rc,
            duration_secs=duration_secs,
            timestamp=self.ts,
        )
        self.save_metadata()

    def compute_common_salt(self) -> str:
        hasher = hashlib.sha256()
        hasher.update(f"agda_bin={self.agda_bin}\n".encode())
        try:
            version = subprocess.run([self.agda_bin, "--version"], cwd=self.root, capture_output=True, text=True, check=False).stdout.splitlines()
            if version:
                hasher.update(version[0].encode())
        except Exception:
            pass
        for rel in ("scripts/run_closure_hygiene.py",):
            path = self.root / rel
            if not path.exists():
                continue
            try:
                data = path.read_bytes()
            except Exception:
                continue
            hasher.update(rel.encode())
            hasher.update(hashlib.sha256(data).digest())
        return hasher.hexdigest()

    def hash_paths(self, rel_paths: Iterable[str], extra_chunks: Iterable[str] = ()) -> str:
        hasher = hashlib.sha256()
        hasher.update(self.common_salt.encode())
        for chunk in extra_chunks:
            hasher.update(chunk.encode())
        for rel in sorted(set(rel_paths)):
            path = self.root / rel
            hasher.update(rel.encode())
            try:
                hasher.update(hashlib.sha256(path.read_bytes()).digest())
            except Exception:
                hasher.update(b"<missing>")
        return hasher.hexdigest()

    def module_key(self, rel_path: str) -> str:
        return f"module:{rel_path}"

    def audit_key(self, name: str) -> str:
        return f"audit:{name}"

    def discover_module_paths(self) -> List[str]:
        proc = subprocess.run(
            ["rg", "--files", "-g", "*.agda"],
            cwd=self.root,
            capture_output=True,
            text=True,
            check=True,
        )
        return sorted(line.strip() for line in proc.stdout.splitlines() if line.strip())

    def import_to_relpath(self, import_name: str) -> Optional[str]:
        rel = import_name.replace(".", "/") + ".agda"
        return rel if (self.root / rel).exists() else None

    def parse_direct_deps(self, rel_path: str) -> Set[str]:
        text = (self.root / rel_path).read_text(encoding="utf-8", errors="ignore")
        deps: Set[str] = set()
        for match in IMPORT_RE.finditer(text):
            rel = self.import_to_relpath(match.group(1))
            if rel:
                deps.add(self.module_key(rel))
        return deps

    def build_tasks(self) -> None:
        module_paths = self.discover_module_paths()
        for rel in module_paths:
            artifact = self.out_dir / "modules" / rel.replace("/", "__").replace(".agda", ".log")
            artifact.parent.mkdir(parents=True, exist_ok=True)
            task = Task(
                key=self.module_key(rel),
                kind="module",
                label=rel,
                artifact=artifact,
                command=[self.agda_bin, "-i", ".", rel],
                deps=self.parse_direct_deps(rel),
            )
            self.tasks[task.key] = task

        self.tasks[self.audit_key("canonical_path_audit")] = Task(
            key=self.audit_key("canonical_path_audit"),
            kind="audit",
            label="canonical_path_audit",
            artifact=self.out_dir / "03_canonical_path_audit.txt",
            command=[
                "bash",
                "-lc",
                "\n".join(
                    [
                        'echo "# Canonical Path Audit"',
                        "echo",
                        'echo "## Canonical bridge imports (expected)"',
                        r'rg -n "import DASHI\.Physics\.Closure\.(ContractionForcesQuadraticTheorem|ContractionQuadraticToSignatureBridgeTheorem|QuadraticToCliffordBridgeTheorem|CanonicalContractionToCliffordBridgeTheorem|PhysicsUnification|CanonicalStageCTheoremBundle)" DASHI || true',
                        "echo",
                        'echo "## Potential alternate-route imports inside closure stack (review)"',
                        r'rg -n "import DASHI\.Geometry\.(QuadraticEmergence|QuadraticFromNorm|QuadraticFromParallelogram|QuadraticFormEmergence)|import DASHI\.Physics\.ContractionQuadraticBridge" DASHI/Physics/Closure || true',
                    ]
                ),
            ],
        )
        self.tasks[self.audit_key("placeholder_postulate_audit")] = Task(
            key=self.audit_key("placeholder_postulate_audit"),
            kind="audit",
            label="placeholder_postulate_audit",
            artifact=self.out_dir / "04_placeholder_postulate_audit.txt",
            command=[
                "bash",
                "-lc",
                "\n".join(
                    [
                        'echo "# Placeholder/Postulate Audit"',
                        "echo",
                        'echo "## postulate declarations"',
                        r'rg -n "^[[:space:]]*postulate\b" DASHI || true',
                        "echo",
                        'echo "## placeholder markers"',
                        r'rg -n "placeholder|to be discharged|TODO" DASHI || true',
                    ]
                ),
            ],
        )
        self.tasks[self.audit_key("closure_status_pointers")] = Task(
            key=self.audit_key("closure_status_pointers"),
            kind="audit",
            label="closure_status_pointers",
            artifact=self.out_dir / "05_closure_status_pointers.txt",
            command=[
                "bash",
                "-lc",
                "\n".join(
                    [
                        'echo "# Closure Status Pointers"',
                        r'rg -n "module DASHI\.Physics\.Closure\.(PhysicsUnification|CanonicalContractionToCliffordBridgeTheorem|CanonicalStageCTheoremBundle|PhysicsClosureFullShift)" DASHI/Physics/Closure -S || true',
                    ]
                ),
            ],
        )

        canonical = self.module_key("DASHI/Physics/Closure/CanonicalStageCTheoremBundle.agda")
        everything = self.module_key("DASHI/Everything.agda")
        summary = self.module_key("DASHI/Physics/Closure/PhysicsClosureValidationSummary.agda")
        if everything in self.tasks:
            self.tasks[everything].deps.add(canonical)
        if summary in self.tasks:
            self.tasks[summary].deps.add(canonical)

        for key, task in self.tasks.items():
            self.reverse_deps.setdefault(key, set())
            for dep in task.deps:
                self.reverse_deps.setdefault(dep, set()).add(key)

        self.task_keys = sorted(self.tasks)
        self.apply_learned_classes()
        self.compute_task_fingerprints()

    def apply_learned_classes(self) -> None:
        for task in self.tasks.values():
            if task.kind == "audit":
                task.learned_class = "audit"
            elif task.label in HEAVY_AGGREGATORS:
                task.learned_class = "aggregator"
            else:
                row = self.metadata.get(task.key)
                if row:
                    task.learned_class = row.learned_class
                else:
                    task.learned_class = "fast"

    def module_rel_closure(self, start_key: str) -> Set[str]:
        seen: Set[str] = set()
        rels: Set[str] = set()
        stack = [start_key]
        while stack:
            key = stack.pop()
            if key in seen:
                continue
            seen.add(key)
            task = self.tasks.get(key)
            if task is None or task.kind != "module":
                continue
            rels.add(task.label)
            for dep in task.deps:
                if dep in self.tasks:
                    stack.append(dep)
        return rels

    def compute_task_fingerprints(self) -> None:
        audit_inputs = sorted(str(p.relative_to(self.root)) for p in (self.root / "DASHI").rglob("*.agda"))
        for task in self.tasks.values():
            if task.kind == "module":
                task.fingerprint = self.hash_paths(
                    self.module_rel_closure(task.key),
                    extra_chunks=[f"kind={task.kind}", f"label={task.label}"],
                )
            else:
                task.fingerprint = self.hash_paths(
                    audit_inputs,
                    extra_chunks=[
                        f"kind={task.kind}",
                        f"label={task.label}",
                        f"cmd={' '.join(task.command)}",
                    ],
                )

    def list_discovered_modules(self) -> int:
        selected = self.select_task_keys(discovery_mode=True)
        for key in selected:
            row = self.metadata.get(key)
            print(
                "\t".join(
                    [
                        key,
                        self.tasks[key].kind,
                        self.tasks[key].learned_class,
                        str(row.duration_secs if row else "unknown"),
                        str(row.rc if row else "unknown"),
                    ]
                )
            )
        return 0

    def select_task_keys(self, discovery_mode: bool = False) -> List[str]:
        selected: List[str] = []
        from_id = self.args.from_stage
        only_ids = self.args.only_ids
        class_filter = self.args.class_filter

        for key, task in self.tasks.items():
            if class_filter and task.learned_class != class_filter:
                continue
            if self.args.exclude_heavy and task.learned_class in {"heavy", "aggregator"}:
                continue
            if only_ids or from_id:
                matched = False
                for alias, alias_key in ALIAS_TO_KEY.items():
                    if alias_key != key:
                        continue
                    if only_ids and alias in only_ids:
                        matched = True
                    if from_id and int(alias) >= int(from_id):
                        matched = True
                if not matched:
                    continue
            selected.append(key)

        if not selected and not discovery_mode and (only_ids or from_id or class_filter):
            return []

        if not selected and not discovery_mode:
            selected = list(self.tasks)

        return self.sort_by_duration(selected)

    def sort_by_duration(self, keys: Iterable[str]) -> List[str]:
        return sorted(
            keys,
            key=lambda key: (
                self.metadata[key].duration_secs if key in self.metadata else 999999,
                self.tasks[key].label,
            ),
        )

    def can_skip(self, task: Task) -> bool:
        if not self.args.cache or self.args.refresh_cache:
            return False
        row = self.metadata.get(task.key)
        return bool(row and row.fingerprint == task.fingerprint and row.rc == 0)

    def task_timeout(self, rung_timeout: Optional[int]) -> Optional[int]:
        return rung_timeout

    def should_stream(self, task: Task) -> bool:
        if self.args.verbose_level >= 2:
            return True
        if self.args.verbose_level == 1 and task.learned_class in {"heavy", "aggregator"}:
            return True
        return False

    def run_task(self, task: Task, timeout_secs: Optional[int]) -> TaskResult:
        start = time.time()
        task.artifact.parent.mkdir(parents=True, exist_ok=True)
        stream = self.should_stream(task)
        with task.artifact.open("a", encoding="utf-8") as artifact:
            artifact.write(f"[timeout] {timeout_secs if timeout_secs is not None else 'none'}\n")
            artifact.write("[cmd] " + " ".join(subprocess.list2cmdline([arg]) if " " in arg else arg for arg in task.command) + "\n")
            artifact.write("---\n")
            artifact.flush()

            proc = subprocess.Popen(
                task.command,
                cwd=self.root,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                text=True,
                bufsize=1,
                start_new_session=True,
            )
            with self.proc_lock:
                self.active_processes[task.key] = proc
            try:
                if stream and proc.stdout is not None:
                    for line in proc.stdout:
                        artifact.write(line)
                        artifact.flush()
                        self._print(f"[{task.label}] {line.rstrip()}")
                elif proc.stdout is not None:
                    for line in proc.stdout:
                        artifact.write(line)
                try:
                    rc = proc.wait(timeout=timeout_secs) if timeout_secs is not None else proc.wait()
                except subprocess.TimeoutExpired:
                    try:
                        os.killpg(proc.pid, signal.SIGTERM)
                    except Exception:
                        proc.terminate()
                    time.sleep(1)
                    try:
                        os.killpg(proc.pid, signal.SIGKILL)
                    except Exception:
                        try:
                            proc.kill()
                        except Exception:
                            pass
                    proc.wait()
                    rc = 124
            finally:
                with self.proc_lock:
                    self.active_processes.pop(task.key, None)

        if self.stop_requested and rc == 0:
            rc = 130
        return TaskResult(task.key, rc, max(0, int(time.time() - start)))

    def runnable_now(self, key: str, selected: Set[str]) -> bool:
        deps = self.tasks[key].deps
        for dep in deps:
            if dep not in selected:
                continue
            if self.pending_status.get(dep) != 0:
                return False
        return True

    def dep_failed_hard(self, key: str, selected: Set[str]) -> bool:
        deps = self.tasks[key].deps
        for dep in deps:
            if dep not in selected:
                continue
            rc = self.pending_status.get(dep)
            if rc is None:
                continue
            if rc not in (0, 124):
                return True
        return False

    def dep_waiting_on_timeout(self, key: str, selected: Set[str]) -> bool:
        for dep in self.tasks[key].deps:
            if dep in selected and self.pending_status.get(dep) == 124:
                return True
        return False

    def mark_skip(self, task: Task) -> None:
        self.pending_status[task.key] = 0
        row = self.metadata[task.key]
        self.pending_duration[task.key] = row.duration_secs
        task.artifact.write_text(
            "\n".join(
                [
                    f"[cached] skip {task.label}",
                    f"[fingerprint] {task.fingerprint}",
                    f"[source] {self.metadata_file}",
                ]
            )
            + "\n",
            encoding="utf-8",
        )
        self._print(f"[skip] {task.label} (cached pass)")
        self.update_metadata_for_result(task, 0, row.duration_secs)

    def process_result(self, result: TaskResult) -> None:
        task = self.tasks[result.key]
        self.pending_status[result.key] = result.rc
        self.pending_duration[result.key] = result.duration_secs
        if result.rc == 0:
            self._print(f"[ok]  {task.label}")
        else:
            self._print(f"[fail] {task.label} (exit {result.rc})")

        if task.kind == "module" and task.label not in HEAVY_AGGREGATORS:
            if result.rc == 0:
                if result.duration_secs >= 120:
                    task.learned_class = "heavy"
                elif result.duration_secs >= 20:
                    task.learned_class = "medium"
                else:
                    task.learned_class = "fast"
        self.update_metadata_for_result(task, result.rc, result.duration_secs)

    def run_once(self, selected_keys: List[str], rung_timeout: Optional[int]) -> None:
        selected_set = set(selected_keys)
        pending: Set[str] = set(selected_keys)
        ready = deque()
        queued: Set[str] = set()
        in_flight: Dict[concurrent.futures.Future[TaskResult], str] = {}

        for key in selected_keys:
            if self.can_skip(self.tasks[key]):
                self.mark_skip(self.tasks[key])
                pending.discard(key)

        def refresh_ready() -> None:
            for key in list(pending):
                if key in queued:
                    continue
                if self.dep_failed_hard(key, selected_set):
                    self.pending_status[key] = 125
                    pending.discard(key)
                    continue
                if self.runnable_now(key, selected_set):
                    ready.append(key)
                    queued.add(key)

        refresh_ready()

        with concurrent.futures.ThreadPoolExecutor(max_workers=self.args.jobs) as executor:
            self.executor = executor
            while pending or in_flight:
                if self.stop_requested and not in_flight:
                    break

                refresh_ready()

                while ready and len(in_flight) < self.args.jobs and not self.stop_requested:
                    key = ready.popleft()
                    task = self.tasks[key]
                    self._print(f"[start] {task.label}")
                    future = executor.submit(self.run_task, task, self.task_timeout(rung_timeout))
                    in_flight[future] = key

                if not in_flight:
                    if not ready:
                        break
                    continue

                done, _ = concurrent.futures.wait(
                    in_flight.keys(),
                    timeout=0.1,
                    return_when=concurrent.futures.FIRST_COMPLETED,
                )
                for future in done:
                    key = in_flight.pop(future)
                    pending.discard(key)
                    try:
                        result = future.result()
                    except Exception:
                        result = TaskResult(key, 1, 0)
                    self.process_result(result)

            if self.stop_requested:
                with self.proc_lock:
                    procs = list(self.active_processes.values())
                for proc in procs:
                    try:
                        os.killpg(proc.pid, signal.SIGTERM)
                    except Exception:
                        try:
                            proc.terminate()
                        except Exception:
                            pass
                done, _ = concurrent.futures.wait(in_flight.keys(), timeout=5)
                for future in done:
                    key = in_flight.pop(future)
                    pending.discard(key)
                    try:
                        result = future.result()
                    except Exception:
                        result = TaskResult(key, 130, 0)
                    self.process_result(result)
                for future, key in list(in_flight.items()):
                    pending.discard(key)
                    self.process_result(TaskResult(key, 130, 0))
            self.executor = None

        for key in list(pending):
            if self.dep_waiting_on_timeout(key, selected_set):
                self.pending_status[key] = 125
            elif key not in self.pending_status:
                self.pending_status[key] = 125

    def run_with_ladder(self, selected_keys: List[str]) -> None:
        if not self.args.timeout_ladder:
            self.run_once(selected_keys, None)
            return

        remaining = list(selected_keys)
        for round_index, rung in enumerate(self.args.timeout_ladder, start=1):
            if not remaining or self.stop_requested:
                break
            self._print(f"[ladder] round {round_index} timeout={rung}s remaining={len(remaining)}")
            round_keys = [key for key in remaining if self.pending_status.get(key) not in (0, 125)]
            if not round_keys:
                break
            self.run_once(round_keys, rung)
            remaining = [key for key in remaining if self.pending_status.get(key) == 124]

        for key in remaining:
            if key not in self.pending_status:
                self.pending_status[key] = 124

    def count_selected_class(self, selected_keys: List[str], class_name: str) -> int:
        return sum(1 for key in selected_keys if self.tasks[key].learned_class == class_name)

    def write_summary(self, selected_keys: List[str]) -> None:
        summary = self.out_dir / "SUMMARY.txt"
        overall = "PASS" if all(self.pending_status.get(key, 999) == 0 for key in selected_keys) else "FAIL"
        lines = [
            f"Closure hygiene run: {self.ts}",
            f"Root: {self.root}",
            f"Agda binary: {self.agda_bin}",
            f"Max workers: {self.args.jobs}",
            f"Verbose: {self.args.verbose_level}",
            f"Stage filter from: {self.args.from_stage or 'none'}",
            f"Stage filter only: {','.join(sorted(self.args.only_ids)) if self.args.only_ids else 'none'}",
            f"Class filter: {self.args.class_filter or 'none'}",
            f"Include heavy: {int(not self.args.exclude_heavy)}",
            f"Cache enabled: {int(self.args.cache)}",
            f"Cache refresh: {int(self.args.refresh_cache)}",
            f"Metadata file: {self.metadata_file}",
            f"Timeout ladder: {','.join(str(x) for x in self.args.timeout_ladder) if self.args.timeout_ladder else 'none'}",
            "",
            "Selected tasks:",
            f"  - total: {len(selected_keys)}",
            f"  - fast: {self.count_selected_class(selected_keys, 'fast')}",
            f"  - medium: {self.count_selected_class(selected_keys, 'medium')}",
            f"  - heavy: {self.count_selected_class(selected_keys, 'heavy')}",
            f"  - aggregator: {self.count_selected_class(selected_keys, 'aggregator')}",
            f"  - audit: {self.count_selected_class(selected_keys, 'audit')}",
            "",
            "Alias checks:",
        ]
        for alias in STAGE_ORDER:
            key = ALIAS_TO_KEY[alias]
            lines.append(f"  - {alias} {self.tasks[key].label if key in self.tasks else key}: {self.pending_status.get(key, 'N/A')}")
        lines.extend(["", f"Overall status: {overall}"])
        failed = [f"  - {self.tasks[key].label}:{self.pending_status.get(key, 999)}" for key in selected_keys if self.pending_status.get(key, 999) != 0]
        if failed:
            lines.extend(["", "Failed steps:", *failed])
        summary.write_text("\n".join(lines) + "\n", encoding="utf-8")

    def run(self) -> int:
        if self.args.list_stages:
            for alias in STAGE_ORDER:
                print(f"{alias}  {ALIAS_TO_KEY[alias]}")
            return 0

        self.build_tasks()
        if self.args.discover_modules:
            return self.list_discovered_modules()

        selected_keys = self.select_task_keys()
        if not selected_keys:
            self._print("[done] PASS. No tasks selected.")
            return 0

        self.run_with_ladder(selected_keys)
        self.save_metadata()
        self.write_summary(selected_keys)

        failures = [key for key in selected_keys if self.pending_status.get(key, 999) != 0]
        if failures:
            self._print("")
            self._print("Failed steps:")
            for key in failures:
                self._print(f"  - {self.tasks[key].label}:{self.pending_status.get(key, 999)}")
            self._print(f"[done] FAIL. Artifacts in {self.out_dir}")
            return 130 if self.stop_requested else 1
        self._print(f"[done] PASS. Artifacts in {self.out_dir}")
        return 0


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(add_help=False)
    parser.add_argument("out_dir", nargs="?")
    parser.add_argument("-j", "--jobs", type=int, default=3)
    parser.add_argument("--from", dest="from_stage")
    parser.add_argument("--only")
    parser.add_argument("--list-stages", action="store_true")
    parser.add_argument("--discover-modules", action="store_true")
    parser.add_argument("--class", dest="class_filter")
    parser.add_argument(
        "--include-heavy",
        dest="exclude_heavy",
        action="store_false",
        help="include learned heavy and aggregator tasks (default: skip them)",
    )
    parser.add_argument(
        "--exclude-heavy",
        dest="exclude_heavy",
        action="store_true",
        help="skip learned heavy and aggregator tasks",
    )
    parser.add_argument("--timeout-ladder")
    parser.add_argument("--no-cache", dest="cache", action="store_false")
    parser.add_argument("--refresh-cache", action="store_true")
    parser.add_argument("--metadata-file", "--cache-file", dest="metadata_file", default=str(DEFAULT_METADATA))
    parser.add_argument("--agda-bin", default="agda")
    parser.add_argument("-v", "--verbose", dest="verbose_level", action="store_const", const=1, default=1)
    parser.add_argument("-V", "--very-verbose", dest="verbose_level", action="store_const", const=2)
    parser.add_argument("-q", "--quiet", dest="verbose_level", action="store_const", const=0)
    parser.add_argument("-h", "--help", action="help")
    parser.set_defaults(exclude_heavy=True)
    args = parser.parse_args()

    if args.jobs < 1:
        parser.error("--jobs must be >= 1")
    if args.from_stage:
        args.from_stage = f"{int(args.from_stage):02d}"
        if args.from_stage not in ALIAS_TO_KEY:
            parser.error(f"unknown --from stage ID: {args.from_stage}")
    args.only_ids = set()
    if args.only:
        for item in args.only.split(","):
            sid = f"{int(item):02d}"
            if sid not in ALIAS_TO_KEY:
                parser.error(f"unknown stage ID in --only: {sid}")
            args.only_ids.add(sid)
    args.timeout_ladder = []
    if args.timeout_ladder:
        for item in args.timeout_ladder.split(","):
            try:
                value = int(item)
            except ValueError as exc:
                raise SystemExit(f"invalid timeout ladder entry: {item}") from exc
            if value < 1:
                raise SystemExit(f"invalid timeout ladder entry: {item}")
            args.timeout_ladder.append(value)
    return args


def main() -> int:
    os.chdir(ROOT_DIR)
    args = parse_args()
    runner = Runner(args)
    return runner.run()


if __name__ == "__main__":
    raise SystemExit(main())
