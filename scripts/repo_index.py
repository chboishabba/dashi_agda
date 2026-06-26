#!/usr/bin/env python3
"""Build and query a conservative repo-local Agda/Markdown symbol index.

This pass is deliberately static and read-only:

- Agda source is the authority.
- Markdown contributes doc mentions and doc links.
- SQLite is the durable index store.
- Queries never rebuild unless --update is passed explicitly.

The parser is intentionally conservative. It prefers stable, mechanically
discoverable facts over inference.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import json
import os
import re
import sqlite3
import subprocess
import sys
import time
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any, Iterable


SCHEMA_VERSION = "2.0.0"
DEFAULT_INDEX_PATH = Path(".repo-index/index.sqlite3")
LANG_AGDA = "agda"
LANG_MD = "md"
REF_BATCH_SIZE = 10000
MAX_BARE_NAME_FANOUT = 8
MIN_BARE_NAME_LENGTH = 4
KNOWN_STATUS_VALUES = {
    "promoted",
    "candidate-only",
    "blocked",
    "external-authority-required",
    "false-promotion",
    "deprecated",
    "unknown",
}
IGNORED_PARTS = {
    ".git",
    ".repo-index",
    ".pytest_cache",
    ".venv",
    ".venv-fluid",
    ".codex_skill_work",
    "__pycache__",
    "build",
    "dist",
    "node_modules",
    "outputs",
    "monster",
    "cubical",
    "temp-DOWNLOADED",
}
ALLOWED_TOPLEVEL = {"DASHI", "Docs", "Kernel", "Verification"}
ALLOWED_DOCS_SUBTREES = {"support", "roadmaps"}

MODULE_RE = re.compile(r"^\s*module\s+([A-Za-z][A-Za-z0-9'.]*)\s+where\b")
AGDA_IMPORT_RE = re.compile(r"^\s*(?:open\s+)?import\s+([A-Za-z][A-Za-z0-9'.]*)")
AGDA_DECL_RE = re.compile(r"^(data|record|postulate)\s+([A-Za-z][A-Za-z0-9']*)\b")
AGDA_SIGNATURE_RE = re.compile(r"^([A-Za-z][A-Za-z0-9']*)\s*:")
AGDA_ASSIGN_RE = re.compile(r"^([A-Za-z][A-Za-z0-9']*)\s*=")
IDENT_RE = re.compile(r"[A-Za-z][A-Za-z0-9']*(?:\.[A-Za-z][A-Za-z0-9']*)*")
MARKDOWN_LINK_RE = re.compile(r"\[[^\]]+\]\(([^)]+)\)")
COMMENT_RE = re.compile(r"^\s*--(.*)$")
SECTION_DIVIDER_RE = re.compile(r"^\s*-{8,}\s*$")


@dataclass(slots=True)
class SymbolRecord:
    symbol_id: str
    name: str
    kind: str
    language: str
    module: str | None
    file: str
    line_start: int
    line_end: int
    status: dict[str, str]
    tags: list[str] = field(default_factory=list)
    requirements: dict[str, list[dict[str, str]]] = field(default_factory=dict)


@dataclass(slots=True)
class FileRecord:
    path: str
    language: str
    module: str | None
    mtime_ns: int
    size: int
    sha256: str
    indexed_at: int
    imports: list[str] = field(default_factory=list)
    doc_links: list[str] = field(default_factory=list)
    symbols: list[str] = field(default_factory=list)


@dataclass(slots=True)
class RefRecord:
    from_symbol: str
    to_symbol: str
    ref_kind: str
    file: str
    line: int
    snippet: str


@dataclass(slots=True)
class PhaseTimer:
    name: str
    start: float = field(default_factory=time.monotonic)

    def finish(self) -> float:
        return max(0.0, time.monotonic() - self.start)


@dataclass(slots=True)
class SymbolCatalog:
    exact_tokens: set[str]
    bare_name_counts: dict[str, int]


def _relpath(path: Path, root: Path) -> str:
    try:
        return path.relative_to(root).as_posix()
    except ValueError:
        return path.as_posix()


def _read_text(path: Path) -> str | None:
    try:
        return path.read_text(encoding="utf-8")
    except OSError:
        return None


def _stable_unique(items: Iterable[str]) -> list[str]:
    seen: set[str] = set()
    out: list[str] = []
    for item in items:
        if item in seen:
            continue
        seen.add(item)
        out.append(item)
    return out


def _normalize_kind(kind: str) -> str:
    return kind.lower().strip()


def _status_from_text(text: str) -> dict[str, str]:
    lowered = text.lower()
    promotion = "unknown"
    authority = "unknown"
    truth = "unknown"

    if any(marker in lowered for marker in ("candidate-only", "candidateonly", "candidate only", "checkedcandidateonly")):
        promotion = "candidate-only"
    if "promotedistrue" in lowered or "promoted ≡ true" in lowered or "promoted true" in lowered:
        promotion = "promoted"
    if "blocked" in lowered:
        promotion = "blocked"
    if "external-authority-required" in lowered:
        authority = "external-authority-required"
    if any(
        marker in lowered
        for marker in (
            "noruntimeauthorityisfalse",
            "no-runtime-authority",
            "runtimeauthorityisfalse",
            "runtime authority is false",
        )
    ):
        authority = "no-runtime-authority"
    if any(
        marker in lowered
        for marker in (
            "notruthpromotion",
            "no-truth-promotion",
            "carrystruthisfalse",
            "truthisfalse",
        )
    ):
        truth = "no-truth-promotion"
    if "truthpromotion" in lowered or "carrystruthistrue" in lowered or "truth is true" in lowered:
        truth = "truth-promotion"

    return {
        "promotion": promotion if promotion in KNOWN_STATUS_VALUES else "unknown",
        "authority": authority if authority in KNOWN_STATUS_VALUES else "unknown",
        "truth": truth if truth in KNOWN_STATUS_VALUES else "unknown",
        "source": "agda",
    }


def _collect_doc_block(lines: list[str], start_index: int) -> str:
    collected: list[str] = []
    idx = start_index - 1
    while idx >= 0:
        line = lines[idx]
        if not line.strip():
            if collected:
                break
            idx -= 1
            continue
        if SECTION_DIVIDER_RE.match(line):
            idx -= 1
            continue
        match = COMMENT_RE.match(line)
        if match:
            text = match.group(1).strip()
            if text:
                collected.append(text)
            idx -= 1
            continue
        break
    collected.reverse()
    return " ".join(collected).strip()


def _is_allowed_relpath(rel_path: str) -> bool:
    parts = Path(rel_path).parts
    if not parts:
        return False
    if any(part in IGNORED_PARTS for part in parts):
        return False
    if len(parts) > 1 and parts[0] not in ALLOWED_TOPLEVEL:
        return False
    if len(parts) > 1 and parts[0] == "Docs" and parts[1] not in ALLOWED_DOCS_SUBTREES:
        return False
    suffix = Path(rel_path).suffix
    return suffix in {".agda", ".md"}


def _iter_files(root: Path) -> list[Path]:
    files: list[Path] = []
    for path in root.rglob("*"):
        if not path.is_file():
            continue
        rel_path = _relpath(path, root)
        if _is_allowed_relpath(rel_path):
            files.append(path)
    return sorted(files)


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _mtime_size(path: Path) -> tuple[int, int]:
    stat = path.stat()
    return stat.st_mtime_ns, stat.st_size


def _best_owner_symbol(symbols: list[SymbolRecord], file_path: str, line_no: int) -> str | None:
    containing = [
        item
        for item in symbols
        if item.file == file_path and item.line_start <= line_no <= item.line_end
    ]
    if not containing:
        return None
    containing.sort(key=lambda item: (item.line_end - item.line_start, item.line_start))
    return containing[0].symbol_id


def _last_ident(token: str) -> str:
    parts = token.split(".")
    return parts[-1] if parts else token


class ProgressTracker:
    def __init__(self, label: str, total: int, *, enabled: bool) -> None:
        self.label = label
        self.total = max(0, total)
        self.enabled = enabled
        self.start = time.monotonic()
        self.done = 0

    def advance(self, detail: str) -> None:
        if not self.enabled:
            self.done += 1
            return
        self.done += 1
        elapsed = max(0.001, time.monotonic() - self.start)
        rate = self.done / elapsed
        remaining = max(0, self.total - self.done)
        eta_seconds = remaining / rate if rate > 0 else 0.0
        print(
            f"[repo-index] {self.label} {self.done}/{self.total} "
            f"elapsed={elapsed:.1f}s eta={eta_seconds:.1f}s: {detail}",
            file=sys.stderr,
            flush=True,
        )


def _connect(index_path: Path) -> sqlite3.Connection:
    index_path.parent.mkdir(parents=True, exist_ok=True)
    conn = sqlite3.connect(index_path)
    conn.row_factory = sqlite3.Row
    conn.create_function("last_ident", 1, _last_ident)
    conn.execute("PRAGMA journal_mode=WAL")
    conn.execute("PRAGMA synchronous=NORMAL")
    conn.execute("PRAGMA foreign_keys=ON")
    conn.execute("PRAGMA temp_store=MEMORY")
    conn.execute("PRAGMA cache_size=-200000")
    conn.execute("PRAGMA busy_timeout=5000")
    return conn


def _ensure_schema(conn: sqlite3.Connection) -> None:
    conn.executescript(
        """
        CREATE TABLE IF NOT EXISTS meta (
            key TEXT PRIMARY KEY,
            value TEXT NOT NULL
        );

        CREATE TABLE IF NOT EXISTS files (
            path TEXT PRIMARY KEY,
            language TEXT NOT NULL,
            module TEXT,
            mtime_ns INTEGER NOT NULL,
            size INTEGER NOT NULL,
            sha256 TEXT NOT NULL,
            indexed_at INTEGER NOT NULL,
            imports_json TEXT NOT NULL,
            doc_links_json TEXT NOT NULL,
            symbols_json TEXT NOT NULL
        );

        CREATE TABLE IF NOT EXISTS symbols (
            symbol_id TEXT PRIMARY KEY,
            name TEXT NOT NULL,
            kind TEXT NOT NULL,
            language TEXT NOT NULL,
            module TEXT,
            file TEXT NOT NULL,
            line_start INTEGER NOT NULL,
            line_end INTEGER NOT NULL,
            status_json TEXT NOT NULL,
            tags_json TEXT NOT NULL,
            requirements_json TEXT NOT NULL,
            FOREIGN KEY(file) REFERENCES files(path) ON DELETE CASCADE
        );

        CREATE TABLE IF NOT EXISTS imports (
            file TEXT NOT NULL,
            imported_module TEXT NOT NULL,
            line INTEGER NOT NULL,
            owner_symbol TEXT,
            FOREIGN KEY(file) REFERENCES files(path) ON DELETE CASCADE
        );

        CREATE TABLE IF NOT EXISTS mentions (
            file TEXT NOT NULL,
            line INTEGER NOT NULL,
            owner_symbol TEXT,
            token TEXT NOT NULL,
            snippet TEXT NOT NULL,
            source_kind TEXT NOT NULL,
            FOREIGN KEY(file) REFERENCES files(path) ON DELETE CASCADE
        );

        CREATE TABLE IF NOT EXISTS refs (
            from_symbol TEXT NOT NULL,
            to_symbol TEXT NOT NULL,
            ref_kind TEXT NOT NULL,
            file TEXT NOT NULL,
            line INTEGER NOT NULL,
            snippet TEXT NOT NULL
        );
        """
    )
    conn.execute(
        "INSERT INTO meta(key, value) VALUES('schema_version', ?) "
        "ON CONFLICT(key) DO UPDATE SET value = excluded.value",
        (SCHEMA_VERSION,),
    )


def _create_lookup_indexes(conn: sqlite3.Connection) -> None:
    conn.executescript(
        """
        CREATE INDEX IF NOT EXISTS idx_symbols_name ON symbols(name);
        CREATE INDEX IF NOT EXISTS idx_symbols_module ON symbols(module);
        CREATE INDEX IF NOT EXISTS idx_symbols_file ON symbols(file);
        CREATE INDEX IF NOT EXISTS idx_imports_file ON imports(file);
        CREATE INDEX IF NOT EXISTS idx_imports_module ON imports(imported_module);
        CREATE INDEX IF NOT EXISTS idx_mentions_token ON mentions(token);
        CREATE INDEX IF NOT EXISTS idx_mentions_file ON mentions(file);
        """
    )


def _create_ref_indexes(conn: sqlite3.Connection) -> None:
    conn.executescript(
        """
        CREATE INDEX IF NOT EXISTS idx_refs_to_symbol ON refs(to_symbol);
        CREATE INDEX IF NOT EXISTS idx_refs_from_symbol ON refs(from_symbol);
        CREATE INDEX IF NOT EXISTS idx_refs_file ON refs(file);
        """
    )


def _create_secondary_indexes(conn: sqlite3.Connection) -> None:
    _create_lookup_indexes(conn)
    _create_ref_indexes(conn)


def _drop_secondary_indexes(conn: sqlite3.Connection) -> None:
    conn.executescript(
        """
        DROP INDEX IF EXISTS idx_symbols_name;
        DROP INDEX IF EXISTS idx_symbols_module;
        DROP INDEX IF EXISTS idx_symbols_file;
        DROP INDEX IF EXISTS idx_imports_file;
        DROP INDEX IF EXISTS idx_imports_module;
        DROP INDEX IF EXISTS idx_mentions_token;
        DROP INDEX IF EXISTS idx_mentions_file;
        DROP INDEX IF EXISTS idx_refs_to_symbol;
        DROP INDEX IF EXISTS idx_refs_from_symbol;
        DROP INDEX IF EXISTS idx_refs_file;
        """
    )


def _drop_data(conn: sqlite3.Connection) -> None:
    conn.executescript(
        """
        DELETE FROM refs;
        DELETE FROM mentions;
        DELETE FROM imports;
        DELETE FROM symbols;
        DELETE FROM files;
        """
    )


def _load_file_row(conn: sqlite3.Connection, rel_path: str) -> sqlite3.Row | None:
    return conn.execute("SELECT * FROM files WHERE path = ?", (rel_path,)).fetchone()


def _load_indexed_paths(conn: sqlite3.Connection) -> set[str]:
    rows = conn.execute("SELECT path FROM files").fetchall()
    return {row["path"] for row in rows}


def _has_index_data(conn: sqlite3.Connection) -> bool:
    row = conn.execute("SELECT COUNT(*) AS count FROM files").fetchone()
    return bool(row and row["count"] > 0)


def _owner_rows_for_file(conn: sqlite3.Connection, file_path: str) -> list[tuple[str, int, int]]:
    rows = conn.execute(
        "SELECT symbol_id, line_start, line_end FROM symbols WHERE file = ? ORDER BY line_start, line_end",
        (file_path,),
    ).fetchall()
    return [
        (row["symbol_id"], int(row["line_start"]), int(row["line_end"]))
        for row in rows
    ]


def _replace_file_records(
    conn: sqlite3.Connection,
    file_record: FileRecord,
    symbols: list[SymbolRecord],
    imports: list[tuple[int, str, str | None]],
) -> None:
    conn.execute("DELETE FROM refs WHERE file = ?", (file_record.path,))
    conn.execute("DELETE FROM mentions WHERE file = ?", (file_record.path,))
    conn.execute("DELETE FROM imports WHERE file = ?", (file_record.path,))
    conn.execute("DELETE FROM symbols WHERE file = ?", (file_record.path,))
    conn.execute("DELETE FROM files WHERE path = ?", (file_record.path,))
    conn.execute(
        """
        INSERT INTO files(path, language, module, mtime_ns, size, sha256, indexed_at, imports_json, doc_links_json, symbols_json)
        VALUES(?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
        """,
        (
            file_record.path,
            file_record.language,
            file_record.module,
            file_record.mtime_ns,
            file_record.size,
            file_record.sha256,
            file_record.indexed_at,
            json.dumps(file_record.imports, sort_keys=True),
            json.dumps(file_record.doc_links, sort_keys=True),
            json.dumps(file_record.symbols, sort_keys=True),
        ),
    )
    conn.executemany(
        """
        INSERT INTO symbols(symbol_id, name, kind, language, module, file, line_start, line_end, status_json, tags_json, requirements_json)
        VALUES(?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
        """,
        [
            (
                symbol.symbol_id,
                symbol.name,
                symbol.kind,
                symbol.language,
                symbol.module,
                symbol.file,
                symbol.line_start,
                symbol.line_end,
                json.dumps(symbol.status, sort_keys=True),
                json.dumps(symbol.tags, sort_keys=True),
                json.dumps(symbol.requirements, sort_keys=True),
            )
            for symbol in symbols
        ],
    )
    conn.executemany(
        "INSERT INTO imports(file, imported_module, line, owner_symbol) VALUES(?, ?, ?, ?)",
        [(file_record.path, imported_module, line_no, owner_symbol) for line_no, imported_module, owner_symbol in imports],
    )


def _replace_mentions(
    conn: sqlite3.Connection,
    file_path: str,
    mentions: list[tuple[int, str | None, str, str, str]],
) -> None:
    conn.execute("DELETE FROM mentions WHERE file = ?", (file_path,))
    conn.executemany(
        "INSERT INTO mentions(file, line, owner_symbol, token, snippet, source_kind) VALUES(?, ?, ?, ?, ?, ?)",
        [(file_path, line_no, owner_symbol, token, snippet, source_kind) for line_no, owner_symbol, token, snippet, source_kind in mentions],
    )


def _delete_file(conn: sqlite3.Connection, rel_path: str) -> None:
    conn.execute("DELETE FROM refs WHERE file = ?", (rel_path,))
    conn.execute("DELETE FROM mentions WHERE file = ?", (rel_path,))
    conn.execute("DELETE FROM imports WHERE file = ?", (rel_path,))
    conn.execute("DELETE FROM symbols WHERE file = ?", (rel_path,))
    conn.execute("DELETE FROM files WHERE path = ?", (rel_path,))


def _parse_agda_file(path: Path, root: Path, sha256: str, indexed_at: int) -> tuple[FileRecord, list[SymbolRecord], list[tuple[int, str, str | None]]]:
    text = _read_text(path)
    rel_path = _relpath(path, root)
    mtime_ns, size = _mtime_size(path)
    if text is None:
        return (
            FileRecord(rel_path, LANG_AGDA, None, mtime_ns, size, sha256, indexed_at),
            [],
            [],
        )

    lines = text.splitlines()
    module_name: str | None = None
    imports: list[tuple[int, str, str | None]] = []
    symbols: list[SymbolRecord] = []

    module_line_no = 1
    for idx, line in enumerate(lines):
        module_match = MODULE_RE.match(line)
        if module_match:
            module_name = module_match.group(1)
            module_line_no = idx + 1
            break

    if module_name:
        symbols.append(
            SymbolRecord(
                symbol_id=module_name,
                name=module_name.split(".")[-1],
                kind="module",
                language=LANG_AGDA,
                module=module_name,
                file=rel_path,
                line_start=module_line_no,
                line_end=module_line_no,
                status={"promotion": "unknown", "authority": "unknown", "truth": "unknown", "source": "agda"},
                tags=["module"],
                requirements={},
            )
        )

    top_level_starts: list[int] = []
    for idx, line in enumerate(lines):
        stripped = line.strip()
        if not stripped or stripped.startswith("--") or SECTION_DIVIDER_RE.match(line):
            continue
        if line[: len(line) - len(line.lstrip())]:
            continue
        if MODULE_RE.match(line) or AGDA_DECL_RE.match(line) or AGDA_SIGNATURE_RE.match(line) or AGDA_ASSIGN_RE.match(line):
            top_level_starts.append(idx)
    top_level_starts = _stable_unique(top_level_starts)
    top_level_starts.append(len(lines))
    seen_symbol_ids = {symbol.symbol_id for symbol in symbols}

    for pos, start in enumerate(top_level_starts[:-1]):
        end = top_level_starts[pos + 1]
        stripped = lines[start].strip()
        if not stripped or stripped.startswith("--"):
            continue

        name: str | None = None
        kind = "value"

        decl_match = AGDA_DECL_RE.match(stripped)
        if decl_match:
            kind = decl_match.group(1).lower()
            name = decl_match.group(2)
        else:
            sig_match = AGDA_SIGNATURE_RE.match(stripped)
            assign_match = AGDA_ASSIGN_RE.match(stripped)
            if sig_match:
                name = sig_match.group(1)
                kind = "function"
            elif assign_match:
                name = assign_match.group(1)
                kind = "value"

        if not name:
            continue

        block_text = "\n".join(lines[start:end])
        doc = _collect_doc_block(lines, start)
        status = _status_from_text(f"{name}\n{stripped}\n{doc}\n{block_text}")
        symbol_id = f"{module_name}.{name}" if module_name else f"{rel_path}::{name}"
        if symbol_id in seen_symbol_ids:
            continue
        seen_symbol_ids.add(symbol_id)
        requirements = {"syntactic_requirements": []}

        symbols.append(
            SymbolRecord(
                symbol_id=symbol_id,
                name=name,
                kind=_normalize_kind(kind),
                language=LANG_AGDA,
                module=module_name,
                file=rel_path,
                line_start=start + 1,
                line_end=end,
                status=status,
                tags=[module_name.split(".")[0]] if module_name else [],
                requirements=requirements,
            )
        )

        if kind == "record":
            field_lines: list[str] = []
            for inner_idx in range(start + 1, end):
                inner = lines[inner_idx]
                inner_stripped = inner.strip()
                if not inner_stripped or inner.lstrip().startswith("field"):
                    continue
                field_match = re.match(r"^\s+([A-Za-z][A-Za-z0-9']*)\s*:", inner)
                if field_match:
                    field_lines.append(field_match.group(1))
            requirements["syntactic_requirements"].extend(
                {"kind": "field", "symbol": field_name, "source": "local-record-field"}
                for field_name in field_lines
            )

    for idx, line in enumerate(lines):
        import_match = AGDA_IMPORT_RE.match(line)
        if import_match:
            owner_symbol = _best_owner_symbol(symbols, rel_path, idx + 1)
            imports.append((idx + 1, import_match.group(1), owner_symbol))

    file_record = FileRecord(
        path=rel_path,
        language=LANG_AGDA,
        module=module_name,
        mtime_ns=mtime_ns,
        size=size,
        sha256=sha256,
        indexed_at=indexed_at,
        imports=_stable_unique(import_name for _line_no, import_name, _owner in imports),
        doc_links=[],
        symbols=[symbol.symbol_id for symbol in symbols],
    )
    return file_record, symbols, imports


def _parse_markdown_file(path: Path, root: Path, sha256: str, indexed_at: int) -> tuple[FileRecord, list[SymbolRecord], list[tuple[int, str, str | None]]]:
    text = _read_text(path)
    rel_path = _relpath(path, root)
    mtime_ns, size = _mtime_size(path)
    if text is None:
        return (
            FileRecord(rel_path, LANG_MD, None, mtime_ns, size, sha256, indexed_at),
            [],
            [],
        )

    lines = text.splitlines()
    doc_links = _stable_unique(MARKDOWN_LINK_RE.findall(text))
    symbol = SymbolRecord(
        symbol_id=f"docs:{rel_path}",
        name=path.stem,
        kind="document",
        language=LANG_MD,
        module=None,
        file=rel_path,
        line_start=1,
        line_end=max(1, len(lines)),
        status={"promotion": "unknown", "authority": "unknown", "truth": "unknown", "source": "docs"},
        tags=["doc"],
        requirements={},
    )
    file_record = FileRecord(
        path=rel_path,
        language=LANG_MD,
        module=None,
        mtime_ns=mtime_ns,
        size=size,
        sha256=sha256,
        indexed_at=indexed_at,
        imports=[],
        doc_links=doc_links,
        symbols=[symbol.symbol_id],
    )
    return file_record, [symbol], []


def _parse_file(path: Path, root: Path, sha256: str, indexed_at: int) -> tuple[FileRecord, list[SymbolRecord], list[tuple[int, str, str | None]]]:
    if path.suffix == ".agda":
        return _parse_agda_file(path, root, sha256, indexed_at)
    return _parse_markdown_file(path, root, sha256, indexed_at)


def _parse_file_task(path: Path, root: Path, indexed_at: int) -> tuple[FileRecord, list[SymbolRecord], list[tuple[int, str, str | None]]]:
    sha256 = _sha256_file(path)
    return _parse_file(path, root, sha256, indexed_at)


def _build_symbol_catalog(conn: sqlite3.Connection) -> SymbolCatalog:
    exact_tokens: set[str] = set()
    bare_name_counts: dict[str, int] = {}
    for row in conn.execute("SELECT symbol_id, module, name FROM symbols"):
        exact_tokens.add(row["symbol_id"])
        bare_name_counts[row["name"]] = bare_name_counts.get(row["name"], 0) + 1
        if row["module"]:
            exact_tokens.add(row["module"])
            module_last = _last_ident(row["module"])
            bare_name_counts[module_last] = bare_name_counts.get(module_last, 0) + 1
    return SymbolCatalog(exact_tokens=exact_tokens, bare_name_counts=bare_name_counts)


def _should_keep_mention(token: str, catalog: SymbolCatalog) -> bool:
    if token in catalog.exact_tokens:
        return True
    last = _last_ident(token)
    if "." in token:
        return last in catalog.bare_name_counts
    if len(token) < MIN_BARE_NAME_LENGTH:
        return False
    return catalog.bare_name_counts.get(token, 0) <= MAX_BARE_NAME_FANOUT


def _extract_mentions_from_path(
    path: Path,
    root: Path,
    owner_rows: list[tuple[str, int, int]],
    catalog: SymbolCatalog,
) -> tuple[str, list[tuple[int, str | None, str, str, str]]]:
    text = _read_text(path)
    rel_path = _relpath(path, root)
    if text is None:
        return rel_path, []

    lines = text.splitlines()
    mentions: list[tuple[int, str | None, str, str, str]] = []
    source_kind = "agda" if path.suffix == ".agda" else "docs"

    for line_no, line in enumerate(lines, start=1):
        stripped = line.strip()
        if not stripped or stripped.startswith("--"):
            continue
        if source_kind == "docs" and not any(ch in stripped for ch in (".", "/", "`")):
            continue
        owner_symbol = _best_owner_symbol_for_rows(owner_rows, line_no)
        for token in _stable_unique(IDENT_RE.findall(line)):
            if not _should_keep_mention(token, catalog):
                continue
            mentions.append((line_no, owner_symbol, token, stripped, source_kind))
    return rel_path, mentions


def _best_owner_symbol_for_rows(owner_rows: list[tuple[str, int, int]], line_no: int) -> str | None:
    containing = [
        (symbol_id, line_end - line_start, line_start)
        for symbol_id, line_start, line_end in owner_rows
        if line_start <= line_no <= line_end
    ]
    if not containing:
        return None
    containing.sort(key=lambda item: (item[1], item[2]))
    return containing[0][0]


def _git_repo_root(root: Path) -> Path | None:
    try:
        result = subprocess.run(
            ["git", "rev-parse", "--show-toplevel"],
            cwd=root,
            check=True,
            text=True,
            capture_output=True,
        )
    except (OSError, subprocess.CalledProcessError):
        return None
    return Path(result.stdout.strip())


def _git_changed_paths(root: Path) -> set[str] | None:
    git_root = _git_repo_root(root)
    if git_root is None:
        return None

    changed: set[str] = set()
    commands = [
        ["git", "diff", "--name-only", "HEAD"],
        ["git", "diff", "--cached", "--name-only"],
        ["git", "ls-files", "--others", "--exclude-standard"],
        ["git", "ls-files", "--deleted"],
    ]
    for command in commands:
        try:
            result = subprocess.run(
                command,
                cwd=root,
                check=True,
                text=True,
                capture_output=True,
            )
        except (OSError, subprocess.CalledProcessError):
            return None
        for line in result.stdout.splitlines():
            candidate = line.strip()
            if not candidate:
                continue
            try:
                rel = Path(candidate).resolve().relative_to(root.resolve()).as_posix()
            except ValueError:
                rel = Path(candidate).as_posix()
            if _is_allowed_relpath(rel):
                changed.add(rel)
    return changed


def _fallback_changed_paths(root: Path, conn: sqlite3.Connection) -> set[str]:
    indexed = {
        row["path"]: (row["mtime_ns"], row["size"])
        for row in conn.execute("SELECT path, mtime_ns, size FROM files")
    }
    seen: set[str] = set()
    changed: set[str] = set()
    for path in _iter_files(root):
        rel_path = _relpath(path, root)
        seen.add(rel_path)
        current = _mtime_size(path)
        previous = indexed.get(rel_path)
        if previous != current:
            changed.add(rel_path)
    changed.update(path for path in indexed if path not in seen)
    return changed


def _check_stale_paths(root: Path, conn: sqlite3.Connection) -> list[dict[str, Any]]:
    git_changed = _git_changed_paths(root)
    candidate_paths = sorted(git_changed) if git_changed is not None else sorted(_fallback_changed_paths(root, conn))
    results: list[dict[str, Any]] = []
    for rel_path in candidate_paths:
        abs_path = root / rel_path
        row = _load_file_row(conn, rel_path)
        if not abs_path.exists():
            results.append({"path": rel_path, "state": "missing"})
            continue
        mtime_ns, size = _mtime_size(abs_path)
        if row is None:
            results.append({"path": rel_path, "state": "new"})
            continue
        if row["mtime_ns"] == mtime_ns and row["size"] == size:
            results.append({"path": rel_path, "state": "probably-fresh"})
        else:
            results.append({"path": rel_path, "state": "stale"})
    return results


def _set_meta(conn: sqlite3.Connection, root: Path, indexed_at: int) -> None:
    conn.execute(
        "INSERT INTO meta(key, value) VALUES('root', ?) ON CONFLICT(key) DO UPDATE SET value = excluded.value",
        (root.as_posix(),),
    )
    conn.execute(
        "INSERT INTO meta(key, value) VALUES('generated_at', ?) ON CONFLICT(key) DO UPDATE SET value = excluded.value",
        (str(indexed_at),),
    )


def _print_phase_summary(phases: dict[str, float], *, enabled: bool) -> None:
    if not enabled:
        return
    for name, seconds in phases.items():
        print(f"[repo-index] phase {name}: {seconds:.2f}s", file=sys.stderr, flush=True)


def _populate_mentions(
    root: Path,
    conn: sqlite3.Connection,
    paths: list[Path],
    *,
    progress: bool = False,
    jobs: int = 1,
    commit_every: int = 100,
) -> int:
    catalog = _build_symbol_catalog(conn)
    tasks = [
        (path, _owner_rows_for_file(conn, _relpath(path, root)))
        for path in paths
        if path.exists()
    ]
    mention_progress = ProgressTracker("mentions", len(tasks), enabled=progress)
    mention_count = 0
    pending_since_commit = 0

    def mention_task(item: tuple[Path, list[tuple[str, int, int]]]) -> tuple[str, list[tuple[int, str | None, str, str, str]]]:
        path, owner_rows = item
        return _extract_mentions_from_path(path, root, owner_rows, catalog)

    with concurrent.futures.ThreadPoolExecutor(max_workers=max(1, jobs)) as executor:
        for rel_path, mentions in executor.map(mention_task, tasks):
            _replace_mentions(conn, rel_path, mentions)
            mention_count += len(mentions)
            pending_since_commit += 1
            mention_progress.advance(rel_path)
            if pending_since_commit >= commit_every:
                conn.commit()
                pending_since_commit = 0

    if pending_since_commit:
        conn.commit()
    return mention_count


def _relink_all(conn: sqlite3.Connection, *, progress: bool = False) -> int:
    conn.execute("DELETE FROM refs")
    conn.execute("DROP TABLE IF EXISTS temp.ref_stage")
    conn.execute(
        """
        CREATE TEMP TABLE ref_stage (
            from_symbol TEXT NOT NULL,
            to_symbol TEXT NOT NULL,
            ref_kind TEXT NOT NULL,
            file TEXT NOT NULL,
            line INTEGER NOT NULL,
            snippet TEXT NOT NULL,
            UNIQUE(from_symbol, to_symbol, ref_kind, file, line, snippet)
        )
        """
    )
    if progress:
        print("[repo-index] link imports", file=sys.stderr, flush=True)
    conn.execute(
        """
        INSERT OR IGNORE INTO ref_stage(from_symbol, to_symbol, ref_kind, file, line, snippet)
        SELECT
            COALESCE(i.owner_symbol, i.file),
            s.symbol_id,
            'import-use',
            i.file,
            i.line,
            ''
        FROM imports i
        JOIN symbols s ON s.symbol_id = i.imported_module
        WHERE COALESCE(i.owner_symbol, i.file) <> s.symbol_id
        """
    )
    conn.execute(
        """
        INSERT OR IGNORE INTO ref_stage(from_symbol, to_symbol, ref_kind, file, line, snippet)
        SELECT
            COALESCE(i.owner_symbol, i.file),
            s.symbol_id,
            'import-use',
            i.file,
            i.line,
            ''
        FROM imports i
        JOIN symbols s ON s.module = i.imported_module
        WHERE COALESCE(i.owner_symbol, i.file) <> s.symbol_id
        """
    )
    if progress:
        print("[repo-index] link mentions", file=sys.stderr, flush=True)
    for predicate in (
        "s.symbol_id = m.token",
        "s.module = m.token",
        "s.name = m.token",
        "instr(m.token, '.') > 0 AND s.name = last_ident(m.token)",
    ):
        conn.execute(
            f"""
            INSERT OR IGNORE INTO ref_stage(from_symbol, to_symbol, ref_kind, file, line, snippet)
            SELECT
                COALESCE(m.owner_symbol, m.file),
                s.symbol_id,
                CASE WHEN m.source_kind = 'docs' THEN 'doc-mention' ELSE 'definition-use' END,
                m.file,
                m.line,
                m.snippet
            FROM mentions m
            JOIN symbols s ON {predicate}
            WHERE COALESCE(m.owner_symbol, m.file) <> s.symbol_id
            """
        )
    conn.execute("INSERT INTO refs SELECT * FROM ref_stage")
    conn.execute("DROP TABLE ref_stage")
    row = conn.execute("SELECT COUNT(*) AS count FROM refs").fetchone()
    return int(row["count"])


def _build_full(
    root: Path,
    conn: sqlite3.Connection,
    *,
    progress: bool = False,
    jobs: int = 1,
    commit_every: int = 100,
) -> dict[str, Any]:
    indexed_at = int(time.time())
    paths = _iter_files(root)
    phases: dict[str, float] = {}

    timer = PhaseTimer("reset")
    _drop_secondary_indexes(conn)
    _drop_data(conn)
    conn.commit()
    phases["reset"] = timer.finish()

    timer = PhaseTimer("parse")
    parse_progress = ProgressTracker("parse", len(paths), enabled=progress)
    file_count = 0
    symbol_count = 0
    pending_since_commit = 0

    with concurrent.futures.ThreadPoolExecutor(max_workers=max(1, jobs)) as executor:
        for file_record, symbols, imports in executor.map(
            lambda path: _parse_file_task(path, root, indexed_at),
            paths,
        ):
            _replace_file_records(conn, file_record, symbols, imports)
            file_count += 1
            symbol_count += len(symbols)
            pending_since_commit += 1
            parse_progress.advance(file_record.path)
            if pending_since_commit >= commit_every:
                conn.commit()
                pending_since_commit = 0

    if pending_since_commit:
        conn.commit()
    phases["parse"] = timer.finish()

    timer = PhaseTimer("mentions")
    mention_count = _populate_mentions(root, conn, paths, progress=progress, jobs=jobs, commit_every=commit_every)
    phases["mentions"] = timer.finish()

    timer = PhaseTimer("link-prepare")
    _create_lookup_indexes(conn)
    conn.commit()
    phases["link-prepare"] = timer.finish()

    timer = PhaseTimer("link")
    ref_count = _relink_all(conn, progress=progress)
    conn.commit()
    phases["link"] = timer.finish()

    timer = PhaseTimer("finalize")
    _create_ref_indexes(conn)
    conn.execute("ANALYZE")
    _set_meta(conn, root, indexed_at)
    conn.commit()
    phases["finalize"] = timer.finish()
    _print_phase_summary(phases, enabled=progress)
    return {
        "files": file_count,
        "symbols": symbol_count,
        "mentions": mention_count,
        "references": ref_count,
        "phases": phases,
    }


def _update_incremental(
    root: Path,
    conn: sqlite3.Connection,
    *,
    progress: bool = False,
    jobs: int = 1,
    commit_every: int = 100,
) -> dict[str, Any]:
    indexed_at = int(time.time())
    changed = _git_changed_paths(root)
    if changed is None:
        changed = _fallback_changed_paths(root, conn)
    phases: dict[str, float] = {}

    timer = PhaseTimer("inspect")
    parsed = 0
    removed = 0
    skipped = 0
    stat_only = 0
    inspect_progress = ProgressTracker("inspect", len(changed), enabled=progress)
    parse_candidates: list[tuple[Path, str, int, int, str | None]] = []
    deleted_paths: list[str] = []

    for rel_path in sorted(changed):
        abs_path = root / rel_path
        row = _load_file_row(conn, rel_path)
        if not abs_path.exists():
            if row is not None:
                deleted_paths.append(rel_path)
            inspect_progress.advance(rel_path)
            continue

        mtime_ns, size = _mtime_size(abs_path)
        if row is not None and row["mtime_ns"] == mtime_ns and row["size"] == size:
            skipped += 1
            inspect_progress.advance(rel_path)
            continue
        parse_candidates.append((abs_path, rel_path, mtime_ns, size, row["sha256"] if row is not None else None))
        inspect_progress.advance(rel_path)
    phases["inspect"] = timer.finish()

    timer = PhaseTimer("prepare")
    _drop_secondary_indexes(conn)
    pending_since_commit = 0
    for rel_path in deleted_paths:
        _delete_file(conn, rel_path)
        removed += 1
        pending_since_commit += 1
        if pending_since_commit >= commit_every:
            conn.commit()
            pending_since_commit = 0
    if pending_since_commit:
        conn.commit()
    phases["prepare"] = timer.finish()

    timer = PhaseTimer("parse")
    parse_progress = ProgressTracker("update-parse", len(parse_candidates), enabled=progress)
    reparsed_paths: list[Path] = []

    def parse_candidate_task(item: tuple[Path, str, int, int, str | None]) -> tuple[str, str, tuple[Any, ...] | None]:
        abs_path, rel_path, mtime_ns, size, old_sha256 = item
        sha256 = _sha256_file(abs_path)
        if old_sha256 is not None and old_sha256 == sha256:
            return ("stat-only", rel_path, (mtime_ns, size, indexed_at, rel_path))
        return ("parsed", rel_path, _parse_file(abs_path, root, sha256, indexed_at))

    pending_since_commit = 0
    with concurrent.futures.ThreadPoolExecutor(max_workers=max(1, jobs)) as executor:
        for result_kind, rel_path, payload in executor.map(parse_candidate_task, parse_candidates):
            if result_kind == "stat-only":
                mtime_ns, size, updated_at, target_path = payload
                conn.execute(
                    "UPDATE files SET mtime_ns = ?, size = ?, indexed_at = ? WHERE path = ?",
                    (mtime_ns, size, updated_at, target_path),
                )
                stat_only += 1
            else:
                file_record, symbols, imports = payload
                _replace_file_records(conn, file_record, symbols, imports)
                reparsed_paths.append(root / rel_path)
                parsed += 1
            pending_since_commit += 1
            parse_progress.advance(rel_path)
            if pending_since_commit >= commit_every:
                conn.commit()
                pending_since_commit = 0

    if pending_since_commit:
        conn.commit()
    phases["parse"] = timer.finish()

    timer = PhaseTimer("mentions")
    mention_count = _populate_mentions(root, conn, reparsed_paths, progress=progress, jobs=jobs, commit_every=commit_every)
    phases["mentions"] = timer.finish()

    timer = PhaseTimer("link-prepare")
    _create_lookup_indexes(conn)
    conn.commit()
    phases["link-prepare"] = timer.finish()

    timer = PhaseTimer("link")
    ref_count = _relink_all(conn, progress=progress)
    conn.commit()
    phases["link"] = timer.finish()

    timer = PhaseTimer("finalize")
    _create_ref_indexes(conn)
    conn.execute("ANALYZE")
    _set_meta(conn, root, indexed_at)
    conn.commit()
    phases["finalize"] = timer.finish()
    _print_phase_summary(phases, enabled=progress)
    return {
        "changed_candidates": len(changed),
        "parsed": parsed,
        "removed": removed,
        "skipped": skipped,
        "stat_only": stat_only,
        "mentions": mention_count,
        "references": ref_count,
        "phases": phases,
    }


def _db_exists(index_path: Path) -> bool:
    return index_path.exists()


def _load_symbols(
    conn: sqlite3.Connection,
    query: str,
    kind: str | None,
    source: str | None,
) -> list[SymbolRecord]:
    clauses = [
        "(symbol_id = ? OR name = ? OR symbol_id LIKE ? OR name LIKE ?)"
    ]
    params: list[Any] = [query, query, f"{query}%", f"{query}%"]
    if kind and kind != "all":
        clauses.append("kind = ?")
        params.append(kind)
    if source and source != "all":
        if source == "docs":
            clauses.append("language = ?")
            params.append(LANG_MD)
        else:
            clauses.append("language = ?")
            params.append(source)
    query_sql = (
        "SELECT * FROM symbols WHERE " + " AND ".join(clauses) +
        " ORDER BY (symbol_id = ?) DESC, (name = ?) DESC, (symbol_id LIKE ?) DESC, (name LIKE ?) DESC, symbol_id"
    )
    params.extend([query, query, f"{query}%", f"{query}%"])
    rows = conn.execute(query_sql, params).fetchall()
    return [
        SymbolRecord(
            symbol_id=row["symbol_id"],
            name=row["name"],
            kind=row["kind"],
            language=row["language"],
            module=row["module"],
            file=row["file"],
            line_start=row["line_start"],
            line_end=row["line_end"],
            status=json.loads(row["status_json"]),
            tags=json.loads(row["tags_json"]),
            requirements=json.loads(row["requirements_json"]),
        )
        for row in rows
    ]


def _load_refs(conn: sqlite3.Connection, symbol_ids: list[str], source: str | None) -> list[RefRecord]:
    if not symbol_ids:
        return []
    placeholders = ", ".join("?" for _ in symbol_ids)
    clauses = [f"to_symbol IN ({placeholders})"]
    params: list[Any] = list(symbol_ids)
    if source and source != "all":
        clauses.append("file IN (SELECT path FROM files WHERE language = ?)")
        params.append(LANG_MD if source == "docs" else source)
    rows = conn.execute(
        "SELECT from_symbol, to_symbol, ref_kind, file, line, snippet FROM refs WHERE " + " AND ".join(clauses) +
        " ORDER BY ref_kind, file, line",
        params,
    ).fetchall()
    return [
        RefRecord(
            from_symbol=row["from_symbol"],
            to_symbol=row["to_symbol"],
            ref_kind=row["ref_kind"],
            file=row["file"],
            line=row["line"],
            snippet=row["snippet"],
        )
        for row in rows
    ]


def _file_imports(conn: sqlite3.Connection, file_path: str) -> list[str]:
    row = conn.execute("SELECT imports_json FROM files WHERE path = ?", (file_path,)).fetchone()
    if row is None:
        return []
    return json.loads(row["imports_json"])


def _freshness_for_symbol(root: Path, conn: sqlite3.Connection, symbol: SymbolRecord) -> dict[str, Any]:
    row = _load_file_row(conn, symbol.file)
    if row is None:
        return {"state": "missing", "file": symbol.file}
    path = root / symbol.file
    if not path.exists():
        return {"state": "missing", "file": symbol.file}
    mtime_ns, size = _mtime_size(path)
    if row["mtime_ns"] == mtime_ns and row["size"] == size:
        return {"state": "fresh", "checked_by": "mtime_ns+size", "file": symbol.file}
    return {"state": "stale", "reason": "mtime_ns_or_size_changed", "file": symbol.file, "recommendation": "run repo-index update"}


def _pretty_symbol(symbol: SymbolRecord) -> str:
    pieces = [
        symbol.symbol_id,
        f"  kind: {symbol.kind}",
        f"  module: {symbol.module or 'unknown'}",
        f"  file: {symbol.file}:{symbol.line_start}",
        f"  status: {symbol.status.get('promotion', 'unknown')}",
    ]
    return "\n".join(pieces)


def _pretty_refs(refs: list[RefRecord]) -> str:
    if not refs:
        return "no references"
    lines: list[str] = []
    current_kind = None
    for ref in refs[:120]:
        if ref.ref_kind != current_kind:
            current_kind = ref.ref_kind
            lines.append(current_kind)
        lines.append(f"  {ref.from_symbol} -> {ref.to_symbol} @ {ref.file}:{ref.line}")
        if ref.snippet:
            lines.append(f"    {ref.snippet}")
    return "\n".join(lines)


def _pretty_reqs(symbol: SymbolRecord, imports: list[str]) -> str:
    lines = [symbol.symbol_id, "  syntactic_requirements:"]
    syntactic = [
        {"kind": "import", "symbol": item, "source": "parsed-import"}
        for item in imports
    ] + list(symbol.requirements.get("syntactic_requirements", []))
    if syntactic:
        for item in syntactic:
            lines.append(f"    - {item.get('kind')}: {item.get('symbol')} ({item.get('source')})")
    else:
        lines.append("    - none")
    lines.append("  semantic_requirements:")
    semantic = symbol.requirements.get("semantic_requirements", [])
    if semantic:
        for item in semantic:
            lines.append(f"    - {item.get('kind')}: {item.get('symbol', item.get('value', ''))} ({item.get('source')})")
    else:
        lines.append("    - none")
    return "\n".join(lines)


def _pretty_hover(symbol: SymbolRecord) -> str:
    return "\n".join(
        [
            symbol.symbol_id,
            f"kind: {symbol.kind}",
            f"module: {symbol.module or 'unknown'}",
            f"file: {symbol.file}:{symbol.line_start}",
            f"status: {symbol.status.get('promotion', 'unknown')}",
        ]
    )


def _pretty_complete(symbols: list[SymbolRecord]) -> str:
    if not symbols:
        return "no matches"
    return "\n".join(f"{symbol.symbol_id} [{symbol.kind}]" for symbol in symbols[:80])


def _graph_node(conn: sqlite3.Connection, symbol: SymbolRecord, depth: int, seen: set[str]) -> dict[str, Any]:
    node = {
        "symbol_id": symbol.symbol_id,
        "name": symbol.name,
        "kind": symbol.kind,
        "module": symbol.module,
        "file": symbol.file,
        "line_start": symbol.line_start,
        "status": symbol.status,
    }
    if depth <= 0 or symbol.symbol_id in seen:
        return node
    seen = set(seen)
    seen.add(symbol.symbol_id)

    outgoing: list[dict[str, Any]] = []
    for imported_module in _file_imports(conn, symbol.file):
        row = conn.execute(
            "SELECT * FROM symbols WHERE symbol_id = ? OR module = ? OR name = ? ORDER BY symbol_id LIMIT 1",
            (imported_module, imported_module, _last_ident(imported_module)),
        ).fetchone()
        if row is None:
            outgoing.append({"symbol_id": imported_module, "kind": "import", "unresolved": True})
            continue
        match = SymbolRecord(
            symbol_id=row["symbol_id"],
            name=row["name"],
            kind=row["kind"],
            language=row["language"],
            module=row["module"],
            file=row["file"],
            line_start=row["line_start"],
            line_end=row["line_end"],
            status=json.loads(row["status_json"]),
            tags=json.loads(row["tags_json"]),
            requirements=json.loads(row["requirements_json"]),
        )
        outgoing.append(_graph_node(conn, match, depth - 1, seen))

    for item in symbol.requirements.get("syntactic_requirements", []):
        target = item.get("symbol", "")
        row = conn.execute(
            "SELECT * FROM symbols WHERE symbol_id = ? OR name = ? ORDER BY symbol_id LIMIT 1",
            (target, target),
        ).fetchone()
        if row is None:
            outgoing.append({"symbol_id": target, "kind": item.get("kind"), "unresolved": True})
            continue
        match = SymbolRecord(
            symbol_id=row["symbol_id"],
            name=row["name"],
            kind=row["kind"],
            language=row["language"],
            module=row["module"],
            file=row["file"],
            line_start=row["line_start"],
            line_end=row["line_end"],
            status=json.loads(row["status_json"]),
            tags=json.loads(row["tags_json"]),
            requirements=json.loads(row["requirements_json"]),
        )
        outgoing.append(_graph_node(conn, match, depth - 1, seen))

    incoming_rows = conn.execute(
        "SELECT from_symbol, ref_kind, file, line FROM refs WHERE to_symbol = ? ORDER BY file, line LIMIT 40",
        (symbol.symbol_id,),
    ).fetchall()
    node["outgoing"] = outgoing
    node["incoming"] = [
        {
            "from_symbol": row["from_symbol"],
            "ref_kind": row["ref_kind"],
            "file": row["file"],
            "line": row["line"],
        }
        for row in incoming_rows
    ]
    return node


def _json_envelope(command: str, query: str | None, root: Path, index_path: Path) -> dict[str, Any]:
    return {
        "schema_version": SCHEMA_VERSION,
        "command": command,
        "query": query,
        "root": _relpath(root, root),
        "index": _relpath(index_path, root) if index_path.is_absolute() else index_path.as_posix(),
    }


def _maybe_update(root: Path, index_path: Path, conn: sqlite3.Connection, args: argparse.Namespace) -> dict[str, Any] | None:
    if not getattr(args, "update", False):
        return None
    with conn:
        return _update_incremental(root, conn, progress=args.progress, jobs=args.jobs, commit_every=args.commit_every)


def _render_command_payload(
    command: str,
    query: str | None,
    root: Path,
    index_path: Path,
    conn: sqlite3.Connection,
    args: argparse.Namespace,
) -> tuple[dict[str, Any], str]:
    payload = _json_envelope(command, query, root, index_path)

    if command == "build":
        with conn:
            stats = _build_full(root, conn, progress=args.progress, jobs=args.jobs, commit_every=args.commit_every)
        payload.update(stats)
        payload["status"] = "written"
        return payload, f"built {stats['symbols']} symbols, {stats['references']} references, {stats['files']} files"

    if command == "update":
        with conn:
            stats = _update_incremental(root, conn, progress=args.progress, jobs=args.jobs, commit_every=args.commit_every)
        payload.update(stats)
        payload["status"] = "written"
        return payload, f"updated {stats['parsed']} files, removed {stats['removed']}, relinked {stats['references']} references"

    if command == "check-stale":
        payload["matches"] = _check_stale_paths(root, conn)
        payload["count"] = len(payload["matches"])
        return payload, "\n".join(f"{item['state']}: {item['path']}" for item in payload["matches"][:200]) or "no stale candidates"

    update_stats = _maybe_update(root, index_path, conn, args)
    if update_stats is not None:
        payload["update"] = update_stats

    kind = args.kind
    source = args.source
    matches = _load_symbols(conn, query or "", kind, source)

    if getattr(args, "check", False):
        payload["freshness"] = {
            symbol.symbol_id: _freshness_for_symbol(root, conn, symbol)
            for symbol in matches[:40]
        }

    if command == "defs":
        payload["matches"] = [asdict(symbol) for symbol in matches]
        return payload, "\n\n".join(_pretty_symbol(symbol) for symbol in matches[:20]) if matches else "no matches"

    if command == "hover":
        payload["matches"] = [asdict(matches[0])] if matches else []
        return payload, _pretty_hover(matches[0]) if matches else "no matches"

    if command == "complete":
        payload["matches"] = [asdict(symbol) for symbol in matches]
        return payload, _pretty_complete(matches)

    if command == "status":
        payload["matches"] = [{"symbol_id": symbol.symbol_id, "status": symbol.status} for symbol in matches]
        return payload, "\n".join(f"{symbol.symbol_id}: {symbol.status.get('promotion', 'unknown')}" for symbol in matches[:20]) if matches else "unknown"

    if command == "reqs":
        if not matches:
            payload["matches"] = []
            return payload, "no matches"
        match = matches[0]
        rendered = asdict(match)
        imports = _file_imports(conn, match.file)
        rendered["requirements"] = {
            "syntactic_requirements": [
                {"kind": "import", "symbol": item, "source": "parsed-import"}
                for item in imports
            ] + list(match.requirements.get("syntactic_requirements", [])),
            "semantic_requirements": list(match.requirements.get("semantic_requirements", [])),
        }
        payload["matches"] = [rendered]
        return payload, _pretty_reqs(match, imports)

    if command == "refs":
        refs = _load_refs(conn, [symbol.symbol_id for symbol in matches], source)
        payload["matches"] = [asdict(ref) for ref in refs]
        return payload, _pretty_refs(refs)

    if command == "graph":
        depth = max(0, int(args.depth or 1))
        graph = [_graph_node(conn, symbol, depth, set()) for symbol in matches[:10]]
        payload["matches"] = graph
        return payload, json.dumps(graph, indent=2, sort_keys=True)

    raise SystemExit(f"unsupported command: {command}")


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true", help="Emit JSON instead of pretty text.")
    parser.add_argument("--pretty", action="store_true", help="Force pretty output.")
    parser.add_argument("--root", type=Path, default=Path("."), help="Repository root.")
    parser.add_argument("--index", type=Path, default=DEFAULT_INDEX_PATH, help="SQLite index path.")
    parser.add_argument("--depth", type=int, default=1, help="Graph traversal depth.")
    parser.add_argument("--kind", default="all", help="Filter by symbol kind.")
    parser.add_argument("--source", default="all", help="Filter by source: agda | docs | all.")
    parser.add_argument("--check", action="store_true", help="Check freshness of matched files using mtime_ns + size.")
    parser.add_argument("--update", action="store_true", help="Run incremental update before query commands.")
    parser.add_argument("--progress", action="store_true", help="Emit phase progress and ETA to stderr during build/update/link.")
    parser.add_argument("--jobs", type=int, default=max(1, min(4, os.cpu_count() or 1)), help="Worker count for hash/parse stages.")
    parser.add_argument("--commit-every", type=int, default=100, help="Commit after this many file updates during build/update.")

    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("build", help="Build the SQLite index from scratch.")
    subparsers.add_parser("update", help="Incrementally update the SQLite index.")
    subparsers.add_parser("check-stale", help="Report likely stale paths without parsing.")
    for command in ("defs", "refs", "reqs", "hover", "complete", "graph", "status"):
        sub = subparsers.add_parser(command, help=f"{command} query")
        sub.add_argument("query")
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    root = args.root.resolve()
    index_path = (root / args.index) if not args.index.is_absolute() else args.index
    db_preexisted = index_path.exists()
    conn = _connect(index_path)
    try:
        _ensure_schema(conn)
        if args.command not in {"build", "update", "check-stale"} and (not db_preexisted or not _has_index_data(conn)):
            raise SystemExit("index missing; run `repo-index build`")

        payload, pretty = _render_command_payload(args.command, getattr(args, "query", None), root, index_path, conn, args)
    finally:
        conn.close()

    if args.json:
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        print(pretty)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except KeyboardInterrupt:
        print("[repo-index] interrupted", file=sys.stderr)
        raise SystemExit(130)
