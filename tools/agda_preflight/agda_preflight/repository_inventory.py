from __future__ import annotations

import hashlib
from pathlib import Path
import sqlite3
import time
from typing import Any, Dict, Iterable, List, Optional, Tuple

from .checker import Checker
from .discovery import make_fingerprint
from .interfaces import interface_from_summary
from .repository_store import ensure_repository_schema


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
            updated_ns INTEGER NOT NULL
        );
        """
    )
    conn.commit()


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
        INSERT OR REPLACE INTO repo_symbols(
            symbol_id, name, kind, language, module, file,
            line_start, line_end, promotion, authority, truth, source
        ) VALUES(?, ?, ?, 'agda', ?, ?, ?, ?, ?, ?, ?, ?)
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
        INSERT OR REPLACE INTO repo_symbol_signatures(
            symbol_id, signature, normalized_signature,
            signature_sha256, body_sha256
        ) VALUES(?, ?, ?, ?, ?)
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


def _purge_agda_inventory(conn: sqlite3.Connection) -> None:
    agda_files = [
        str(row[0])
        for row in conn.execute("SELECT path FROM repo_files WHERE language='agda'")
    ]
    if agda_files:
        placeholders = ",".join("?" for _ in agda_files)
        conn.execute(
            "DELETE FROM repo_refs WHERE file IN ({})".format(placeholders),
            agda_files,
        )
    conn.execute("DELETE FROM repo_files WHERE language='agda'")
    conn.execute("DELETE FROM repo_inventory_receipts")


def refresh_repository_inventory(
    root: Path,
    conn: sqlite3.Connection,
) -> Dict[str, Any]:
    """Refresh whole-repo Agda identity/signature inventory from preflight AST.

    This is the canonical producer for the unified repository database. The
    historical `scripts/repo_index.py` database is only a migration source.
    """

    root = root.resolve()
    ensure_inventory_schema(conn)
    status = _existing_status(conn)
    checker = Checker(root)
    files = checker.repository_agda_files()
    errors: List[Dict[str, str]] = []
    symbol_count = 0
    import_count = 0
    started = time.perf_counter_ns()

    _purge_agda_inventory(conn)

    for path in files:
        relative = path.resolve().relative_to(root).as_posix()
        stat = path.stat()
        source_hash = _source_hash(path)
        try:
            summary = checker.parse_summary(path)
            interface = interface_from_summary(root, summary)
        except Exception as error:  # parser failures are recorded, never hidden
            conn.execute(
                """
                INSERT OR REPLACE INTO repo_inventory_receipts(
                    path, source_sha256, parsed, error, updated_ns
                ) VALUES(?, ?, 0, ?, ?)
                """,
                (relative, source_hash, type(error).__name__ + ": " + str(error), time.time_ns()),
            )
            errors.append({"path": relative, "error": type(error).__name__ + ": " + str(error)})
            continue

        module = summary.module_name
        conn.execute(
            """
            INSERT OR REPLACE INTO repo_files(
                path, language, module, mtime_ns, size, sha256, indexed_at
            ) VALUES(?, 'agda', ?, ?, ?, ?, ?)
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
            INSERT OR REPLACE INTO repo_inventory_receipts(
                path, source_sha256, parsed, error, updated_ns
            ) VALUES(?, ?, 1, NULL, ?)
            """,
            (relative, source_hash, time.time_ns()),
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
            import_count += 1

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
        symbol_count += 1

        signature_map = {item.name: item for item in interface.signatures}
        for name, item in sorted(summary.ast.signatures.items()):
            interface_item = signature_map.get(name)
            refs = (
                (interface_item.terminal_head,)
                if interface_item is not None and interface_item.terminal_head
                else ()
            )
            body = "\n".join(clause.rhs_text for clause in summary.ast.clauses.get(name, ()) if clause.rhs_text)
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
            symbol_count += 1

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
            symbol_count += 1
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
                symbol_count += 1
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
                symbol_count += 1

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
            symbol_count += 1
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
                symbol_count += 1

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
            symbol_count += 1

    conn.execute(
        "INSERT INTO repository_meta(key, value) VALUES('inventory_producer', 'agda-preflight') "
        "ON CONFLICT(key) DO UPDATE SET value=excluded.value"
    )
    conn.execute(
        "INSERT INTO repository_meta(key, value) VALUES('inventory_updated_ns', ?) "
        "ON CONFLICT(key) DO UPDATE SET value=excluded.value",
        (str(time.time_ns()),),
    )
    conn.commit()
    return {
        "files": len(files),
        "symbols": symbol_count,
        "imports": import_count,
        "parse_errors": len(errors),
        "errors": errors,
        "elapsed_ms": round((time.perf_counter_ns() - started) / 1_000_000.0, 3),
    }
