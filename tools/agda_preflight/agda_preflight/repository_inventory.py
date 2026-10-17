from __future__ import annotations

import hashlib
from pathlib import Path
import sqlite3
import time
from typing import Any, Callable, Dict, Iterable, List, Optional, Tuple

from .checker import Checker
from .discovery import make_fingerprint
from .interfaces import interface_from_summary
from .repository_store import ensure_repository_schema


DEFAULT_INVENTORY_BATCH_SIZE = 500


def configure_inventory_pragmas(conn: sqlite3.Connection) -> None:
    """Apply memory/cache settings that prevent dirty-page WAL spill storms."""

    conn.execute("PRAGMA temp_store=MEMORY")
    conn.execute("PRAGMA cache_size=-262144")
    conn.execute("PRAGMA cache_spill=OFF")


def ensure_inventory_schema(conn: sqlite3.Connection) -> None:
    ensure_repository_schema(conn)
    conn.executescript(
        """
        CREATE TABLE IF NOT EXISTS repo_symbol_signatures (
            symbol_id TEXT PRIMARY KEY
                REFERENCES repo_symbols(symbol_id) ON DELETE CASCADE,
            signature TEXT NOT NULL,
            normalized_signature TEXT NOT NULL,
            signature_sha256 TEXT NOT NULL,
            body_sha256 TEXT NOT NULL
        );
        CREATE INDEX IF NOT EXISTS repo_symbol_signatures_hash
            ON repo_symbol_signatures(signature_sha256);
        CREATE INDEX IF NOT EXISTS repo_symbol_body_hash
            ON repo_symbol_signatures(body_sha256);

        CREATE TABLE IF NOT EXISTS repo_inventory_receipts (
            path TEXT PRIMARY KEY,
            source_sha256 TEXT NOT NULL,
            parsed INTEGER NOT NULL,
            error TEXT,
            updated_ns INTEGER NOT NULL,
            generation INTEGER NOT NULL DEFAULT 0
        );
        """
    )
    cols = {
        str(row[1])
        for row in conn.execute("PRAGMA table_info(repo_inventory_receipts)").fetchall()
    }
    if "generation" not in cols:
        conn.execute(
            "ALTER TABLE repo_inventory_receipts ADD COLUMN generation INTEGER NOT NULL DEFAULT 0"
        )
    conn.commit()


def _meta_get(conn: sqlite3.Connection, key: str, default: str = "") -> str:
    row = conn.execute(
        "SELECT value FROM repository_meta WHERE key=?",
        (key,),
    ).fetchone()
    return str(row[0]) if row is not None else default


def _meta_set(conn: sqlite3.Connection, key: str, value: str) -> None:
    conn.execute(
        "INSERT INTO repository_meta(key, value) VALUES(?, ?) "
        "ON CONFLICT(key) DO UPDATE SET value=excluded.value",
        (key, value),
    )


def _source_hash(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _qualified(module: str, name: str) -> str:
    if name.startswith(module + "."):
        return name
    return module + "." + name


def _existing_status(conn: sqlite3.Connection) -> Dict[str, Tuple[str, str, str, str]]:
    try:
        rows = conn.execute(
            "SELECT symbol_id, promotion, authority, truth, source FROM repo_symbols"
        ).fetchall()
    except sqlite3.DatabaseError:
        return {}
    return {
        str(row[0]): (str(row[1]), str(row[2]), str(row[3]), str(row[4]))
        for row in rows
    }


def _insert_symbol(
    conn: sqlite3.Connection,
    *,
    status: Dict[str, Tuple[str, str, str, str]],
    symbol_id: str,
    name: str,
    kind: str,
    module: str,
    file: str,
    line_start: int,
    line_end: Optional[int] = None,
    signature: str = "",
    body: str = "",
    refs: Iterable[str] = (),
) -> None:
    promotion, authority, truth, source = status.get(
        symbol_id,
        ("unknown", "unknown", "unknown", "agda"),
    )
    conn.execute(
        """
        INSERT INTO repo_symbols(
            symbol_id, name, kind, language, module, file,
            line_start, line_end, promotion, authority, truth, source
        ) VALUES(?, ?, ?, 'agda', ?, ?, ?, ?, ?, ?, ?, ?)
        ON CONFLICT(symbol_id) DO UPDATE SET
            name=excluded.name,
            kind=excluded.kind,
            language=excluded.language,
            module=excluded.module,
            file=excluded.file,
            line_start=excluded.line_start,
            line_end=excluded.line_end,
            promotion=excluded.promotion,
            authority=excluded.authority,
            truth=excluded.truth,
            source=excluded.source
        """,
        (
            symbol_id,
            name,
            kind,
            module,
            file,
            max(1, int(line_start)),
            max(1, int(line_end if line_end is not None else line_start)),
            promotion,
            authority,
            truth,
            source,
        ),
    )
    fingerprint = make_fingerprint(signature, body)
    conn.execute(
        """
        INSERT INTO repo_symbol_signatures(
            symbol_id, signature, normalized_signature,
            signature_sha256, body_sha256
        ) VALUES(?, ?, ?, ?, ?)
        ON CONFLICT(symbol_id) DO UPDATE SET
            signature=excluded.signature,
            normalized_signature=excluded.normalized_signature,
            signature_sha256=excluded.signature_sha256,
            body_sha256=excluded.body_sha256
        """,
        (
            symbol_id,
            signature,
            fingerprint.normalized_signature,
            fingerprint.signature_sha256,
            fingerprint.body_sha256,
        ),
    )
    for ref in refs:
        if not ref:
            continue
        target = str(ref)
        conn.execute(
            """
            INSERT INTO repo_refs(
                from_symbol, to_symbol, ref_kind, file, line, snippet
            ) VALUES(?, ?, 'interface-reference', ?, ?, ?)
            """,
            (symbol_id, target, file, max(1, int(line_start)), target),
        )


def _purge_file_inventory(conn: sqlite3.Connection, relative: str) -> None:
    conn.execute("DELETE FROM repo_refs WHERE file=?", (relative,))
    conn.execute("DELETE FROM repo_file_imports WHERE file=?", (relative,))
    conn.execute("DELETE FROM repo_symbols WHERE file=? AND language='agda'", (relative,))


def _remove_deleted_files(conn: sqlite3.Connection, stale_paths: Iterable[str]) -> None:
    for relative in stale_paths:
        conn.execute("DELETE FROM repo_refs WHERE file=?", (relative,))
        conn.execute("DELETE FROM repo_files WHERE path=? AND language='agda'", (relative,))
        conn.execute("DELETE FROM repo_inventory_receipts WHERE path=?", (relative,))


def refresh_repository_inventory(
    root: Path,
    conn: sqlite3.Connection,
    *,
    progress: Optional[Callable[[int, int, str], None]] = None,
    batch_size: int = DEFAULT_INVENTORY_BATCH_SIZE,
    resume: bool = True,
) -> Dict[str, Any]:
    """Refresh whole-repo Agda identity/signature inventory from preflight AST.

    This is the canonical producer for the unified repository database. The
    historical `scripts/repo_index.py` database is only a migration source.

    Refresh runs in bounded file batches (`batch_size`) with a durable generation
    and cursor in `repository_meta`. If a run is interrupted mid-way, the next
    invocation with `resume=True` resumes the incomplete generation from its
    committed cursor rather than discarding prior work.
    """

    root = root.resolve()
    if conn.in_transaction:
        conn.commit()
    configure_inventory_pragmas(conn)
    ensure_inventory_schema(conn)

    completed_gen = int(_meta_get(conn, "inventory_generation", "0") or "0")
    target_gen = int(_meta_get(conn, "inventory_target_generation", "0") or "0")
    gen_state = _meta_get(conn, "inventory_generation_state", "")
    saved_cursor = _meta_get(conn, "inventory_cursor", "")

    if resume and gen_state == "in-progress" and target_gen > 0:
        active_generation = target_gen
        resume_cursor = saved_cursor
    else:
        active_generation = max(completed_gen, target_gen) + 1
        resume_cursor = ""
        conn.execute("BEGIN IMMEDIATE")
        try:
            _meta_set(conn, "inventory_target_generation", str(active_generation))
            _meta_set(conn, "inventory_generation_state", "in-progress")
            _meta_set(conn, "inventory_cursor", "")
            conn.commit()
        except Exception:
            if conn.in_transaction:
                conn.rollback()
            raise

    status = _existing_status(conn)
    existing_files = {
        str(row[0]): (int(row[1]), int(row[2]), str(row[3]))
        for row in conn.execute(
            "SELECT path, mtime_ns, size, sha256 FROM repo_files WHERE language='agda'"
        ).fetchall()
    }
    existing_receipts = {
        str(row[0]): (str(row[1]), int(row[2]), row[3], int(row[4]))
        for row in conn.execute(
            "SELECT path, source_sha256, parsed, error, generation FROM repo_inventory_receipts"
        ).fetchall()
    }

    checker = Checker(root)
    indexed_entries: List[Tuple[str, Path]] = sorted(
        (
            (path.relative_to(root).as_posix(), path)
            for path in checker.repository_agda_files()
        ),
        key=lambda item: item[0],
    )
    total = len(indexed_entries)
    expected_paths = {rel for rel, _ in indexed_entries}
    started = time.perf_counter_ns()
    resumed_files = 0
    indexed_files_run = 0
    batches_committed = 0
    effective_batch_size = max(1, int(batch_size))

    for batch_start in range(0, total, effective_batch_size):
        batch = indexed_entries[batch_start : batch_start + effective_batch_size]
        # Fast-path when resuming: if the entire batch is at or before resume_cursor
        # and every file in the batch was already committed in active_generation with
        # matching mtime_ns and size, skip without opening a write transaction.
        to_process: List[Tuple[int, str, Path, Any]] = []
        for offset, (relative, path) in enumerate(batch, start=batch_start + 1):
            if progress is not None:
                progress(offset, total, relative)
            stat = path.stat()
            if resume_cursor and relative <= resume_cursor:
                receipt = existing_receipts.get(relative)
                file_row = existing_files.get(relative)
                if (
                    receipt is not None
                    and receipt[3] == active_generation
                    and (
                        (
                            receipt[1] == 1
                            and file_row is not None
                            and file_row[0] == stat.st_mtime_ns
                            and file_row[1] == stat.st_size
                        )
                        or receipt[1] == 0
                    )
                ):
                    resumed_files += 1
                    continue
            to_process.append((offset, relative, path, stat))

        if not to_process:
            continue

        conn.execute("BEGIN IMMEDIATE")
        try:
            for _offset, relative, path, stat in to_process:
                if relative in existing_files or relative in existing_receipts:
                    _purge_file_inventory(conn, relative)
                source_hash = _source_hash(path)
                try:
                    summary = checker.parse_summary(path)
                    interface = interface_from_summary(root, summary)
                except Exception as error:  # parser failures are recorded, never hidden
                    err_text = type(error).__name__ + ": " + str(error)
                    conn.execute(
                        "DELETE FROM repo_files WHERE path=? AND language='agda'",
                        (relative,),
                    )
                    conn.execute(
                        """
                        INSERT INTO repo_inventory_receipts(
                            path, source_sha256, parsed, error, updated_ns, generation
                        ) VALUES(?, ?, 0, ?, ?, ?)
                        ON CONFLICT(path) DO UPDATE SET
                            source_sha256=excluded.source_sha256,
                            parsed=0,
                            error=excluded.error,
                            updated_ns=excluded.updated_ns,
                            generation=excluded.generation
                        """,
                        (relative, source_hash, err_text, time.time_ns(), active_generation),
                    )
                    indexed_files_run += 1
                    continue

                module = summary.module_name
                conn.execute(
                    """
                    INSERT INTO repo_files(
                        path, language, module, mtime_ns, size, sha256, indexed_at
                    ) VALUES(?, 'agda', ?, ?, ?, ?, ?)
                    ON CONFLICT(path) DO UPDATE SET
                        language='agda',
                        module=excluded.module,
                        mtime_ns=excluded.mtime_ns,
                        size=excluded.size,
                        sha256=excluded.sha256,
                        indexed_at=excluded.indexed_at
                    """,
                    (
                        relative,
                        module,
                        stat.st_mtime_ns,
                        stat.st_size,
                        source_hash,
                        int(time.time()),
                    ),
                )
                conn.execute(
                    """
                    INSERT INTO repo_inventory_receipts(
                        path, source_sha256, parsed, error, updated_ns, generation
                    ) VALUES(?, ?, 1, NULL, ?, ?)
                    ON CONFLICT(path) DO UPDATE SET
                        source_sha256=excluded.source_sha256,
                        parsed=1,
                        error=NULL,
                        updated_ns=excluded.updated_ns,
                        generation=excluded.generation
                    """,
                    (relative, source_hash, time.time_ns(), active_generation),
                )

                for imported in summary.ast.imports:
                    conn.execute(
                        """
                        INSERT OR IGNORE INTO repo_file_imports(
                            file, imported_module, line, owner_symbol
                        ) VALUES(?, ?, ?, NULL)
                        """,
                        (relative, imported.module, int(imported.line)),
                    )

                _insert_symbol(
                    conn,
                    status=status,
                    symbol_id=module,
                    name=module.rsplit(".", 1)[-1],
                    kind="module",
                    module=module,
                    file=relative,
                    line_start=1,
                )

                signature_map = {item.name: item for item in interface.signatures}
                for name, item in sorted(summary.ast.signatures.items()):
                    interface_item = signature_map.get(name)
                    refs = (
                        (interface_item.terminal_head,)
                        if interface_item is not None and interface_item.terminal_head
                        else ()
                    )
                    body = "\n".join(
                        clause.rhs_text
                        for clause in summary.ast.clauses.get(name, ())
                        if clause.rhs_text
                    )
                    _insert_symbol(
                        conn,
                        status=status,
                        symbol_id=_qualified(module, name),
                        name=name,
                        kind="signature",
                        module=module,
                        file=relative,
                        line_start=item.line,
                        signature=item.type_text,
                        body=body,
                        refs=refs,
                    )

                record_map = {item.name: item for item in interface.records}
                for name, record in sorted(summary.ast.records.items()):
                    _insert_symbol(
                        conn,
                        status=status,
                        symbol_id=_qualified(module, name),
                        name=name,
                        kind="record",
                        module=module,
                        file=relative,
                        line_start=record.line,
                    )
                    if record.constructor:
                        _insert_symbol(
                            conn,
                            status=status,
                            symbol_id=_qualified(module, record.constructor),
                            name=record.constructor,
                            kind="constructor",
                            module=module,
                            file=relative,
                            line_start=record.line,
                            refs=(name,),
                        )
                    interface_record = record_map.get(name)
                    interface_fields = (
                        {field.name: field for field in interface_record.fields}
                        if interface_record is not None
                        else {}
                    )
                    for field_name, field in sorted(record.fields.items()):
                        iface = interface_fields.get(field_name)
                        refs = [name]
                        if iface is not None and iface.terminal_head:
                            refs.append(iface.terminal_head)
                        _insert_symbol(
                            conn,
                            status=status,
                            symbol_id=_qualified(module, field_name),
                            name=field_name,
                            kind="field",
                            module=module,
                            file=relative,
                            line_start=field.line,
                            signature=field.type_text,
                            refs=refs,
                        )

                for name, data in sorted(summary.ast.data.items()):
                    _insert_symbol(
                        conn,
                        status=status,
                        symbol_id=_qualified(module, name),
                        name=name,
                        kind="data",
                        module=module,
                        file=relative,
                        line_start=data.line,
                    )
                    for constructor_name, constructor in sorted(data.constructors.items()):
                        _insert_symbol(
                            conn,
                            status=status,
                            symbol_id=_qualified(module, constructor_name),
                            name=constructor_name,
                            kind="constructor",
                            module=module,
                            file=relative,
                            line_start=constructor.line,
                            signature=constructor.type_text,
                            refs=(name,),
                        )

                for nested in sorted(summary.ast.nested_modules):
                    _insert_symbol(
                        conn,
                        status=status,
                        symbol_id=_qualified(module, nested),
                        name=nested.rsplit(".", 1)[-1],
                        kind="module",
                        module=module,
                        file=relative,
                        line_start=1,
                    )
                indexed_files_run += 1

            _meta_set(conn, "inventory_cursor", batch[-1][0])
            conn.commit()
            batches_committed += 1
        except Exception:
            if conn.in_transaction:
                conn.rollback()
            raise

        conn.execute("PRAGMA wal_checkpoint(PASSIVE)")

    stale_paths = (set(existing_files) | set(existing_receipts)) - expected_paths
    conn.execute("BEGIN IMMEDIATE")
    try:
        if stale_paths:
            _remove_deleted_files(conn, sorted(stale_paths))
        _meta_set(conn, "inventory_producer", "agda-preflight")
        _meta_set(conn, "inventory_generation", str(active_generation))
        _meta_set(conn, "inventory_target_generation", str(active_generation))
        _meta_set(conn, "inventory_generation_state", "complete")
        _meta_set(conn, "inventory_cursor", "")
        _meta_set(conn, "inventory_updated_ns", str(time.time_ns()))
        conn.commit()
    except Exception:
        if conn.in_transaction:
            conn.rollback()
        raise

    conn.execute("PRAGMA wal_checkpoint(TRUNCATE)")

    symbol_count = int(
        conn.execute(
            "SELECT count(*) FROM repo_symbols WHERE language='agda'"
        ).fetchone()[0]
    )
    import_count = int(
        conn.execute("SELECT count(*) FROM repo_file_imports").fetchone()[0]
    )
    errors = [
        {"path": str(row[0]), "error": str(row[1] or "parse failure")}
        for row in conn.execute(
            "SELECT path, error FROM repo_inventory_receipts WHERE parsed=0 ORDER BY path"
        ).fetchall()
    ]
    return {
        "files": total,
        "symbols": symbol_count,
        "imports": import_count,
        "parse_errors": len(errors),
        "errors": errors,
        "generation": active_generation,
        "resumed_files": resumed_files,
        "indexed_files": indexed_files_run,
        "batches": batches_committed,
        "elapsed_ms": round((time.perf_counter_ns() - started) / 1_000_000.0, 3),
    }
