from __future__ import annotations

from collections import defaultdict
from pathlib import Path
import hashlib
import re
import sqlite3


ROUND_RE = re.compile(r"Round\d+")

REQUIRED_TABLES = {
    "repo_files": {"path", "module"},
    "repo_file_imports": {"file", "imported_module"},
    "repo_symbols": {"symbol_id", "file", "name", "module", "kind"},
    "repo_symbol_signatures": {
        "symbol_id",
        "normalized_signature",
        "signature_sha256",
        "body_sha256",
    },
}


def connect(db: Path) -> sqlite3.Connection:
    conn = sqlite3.connect(f"file:{db}?mode=ro", uri=True)
    conn.row_factory = sqlite3.Row
    validate_schema(conn)
    return conn


def validate_schema(conn: sqlite3.Connection) -> None:
    tables = {
        r[0]
        for r in conn.execute(
            "SELECT name FROM sqlite_master WHERE type='table'"
        )
    }

    missing_tables = set(REQUIRED_TABLES) - tables
    if missing_tables:
        raise SystemExit(
            f"missing required tables: {sorted(missing_tables)}"
        )

    for table, columns in REQUIRED_TABLES.items():
        have = {
            r[1]
            for r in conn.execute(f"PRAGMA table_info({table})")
        }
        missing = columns - have
        if missing:
            raise SystemExit(
                f"{table}: missing columns {sorted(missing)}"
            )


def is_round(module: str | None) -> bool:
    return bool(module and ROUND_RE.search(module))


def family_of(module: str) -> str:
    return re.sub(r"Round\d+.*$", "", module)


def load_import_graph(conn):
    imports = defaultdict(set)
    reverse = defaultdict(set)

    for r in conn.execute(
        """
        SELECT
            f.module AS importer,
            i.imported_module AS imported
        FROM repo_file_imports i
        JOIN repo_files f ON f.path = i.file
        WHERE f.module != ''
          AND i.imported_module != ''
        """
    ):
        imports[r["importer"]].add(r["imported"])
        reverse[r["imported"]].add(r["importer"])

    return imports, reverse


def module_paths(conn):
    return {
        r["module"]: r["path"]
        for r in conn.execute(
            """
            SELECT module, path
            FROM repo_files
            WHERE module != ''
            """
        )
    }


def closure(imports, roots, available):
    out = set()
    stack = list(roots)

    while stack:
        module = stack.pop()

        if module in out:
            continue

        out.add(module)

        for imported in imports.get(module, ()):
            if imported in available and imported not in out:
                stack.append(imported)

    return out


def decls_for_modules(conn, modules, chunk=400):
    modules = list(modules)
    rows = []

    for i in range(0, len(modules), chunk):
        part = modules[i : i + chunk]

        if not part:
            continue

        q = ",".join("?" for _ in part)

        rows.extend(
            conn.execute(
                f"""
                SELECT
                    s.symbol_id,
                    s.module,
                    s.file,
                    s.name,
                    s.kind,
                    ss.normalized_signature,
                    ss.signature_sha256,
                    ss.body_sha256
                FROM repo_symbols s
                JOIN repo_symbol_signatures ss USING(symbol_id)
                WHERE s.module IN ({q})
                  AND s.kind = 'signature'
                  AND ss.signature_sha256 != ''
                """,
                part,
            ).fetchall()
        )

    return rows


def indexes(decls):
    exact = defaultdict(list)
    sig = defaultdict(list)
    name = defaultdict(list)

    for d in decls:
        exact[
            (
                d["signature_sha256"],
                d["body_sha256"],
            )
        ].append(d)

        sig[d["signature_sha256"]].append(d)
        name[d["name"]].append(d)

    return exact, sig, name


def stable_id(*parts):
    payload = "\0".join(
        str(x or "")
        for x in parts
    )

    return hashlib.sha256(
        payload.encode()
    ).hexdigest()[:20]
