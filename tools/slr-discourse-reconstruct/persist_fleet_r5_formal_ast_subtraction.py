#!/usr/bin/env python3
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
import os
from pathlib import Path
import re
import sys
from typing import Any, Iterable, Mapping, Sequence

SCHEMA = "sensiblaw.r5-formal-ast-subtraction.v1"
DOCUMENT_GRAPH_REF = (
    "pnf-document-graph:"
    "d14f740cb5ec4b39f22998832691f5932bae5e527118280f648f607b57456fc7"
)
EXPECTED_COUNTS = {
    "discharged_core_knowledge": 584,
    "polarity_contradiction_gap": 44,
    "unformalised_formal_gap": 58,
}
EXPECTED_TOTAL = sum(EXPECTED_COUNTS.values())
FORBIDDEN_CHAT_KEYS = {
    "text",
    "content",
    "body",
    "message",
    "transcript",
    "prompt",
    "response",
    "title",
    "summary",
}
SAFE_NAME = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*$")


class R5PersistenceError(RuntimeError):
    pass


def _canonical_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def _normalise_coordinate(value: Mapping[str, Any]) -> dict[str, str]:
    if not isinstance(value, Mapping):
        raise R5PersistenceError("chat coordinate must be an object")
    forbidden = sorted(k for k in value if str(k).lower() in FORBIDDEN_CHAT_KEYS)
    if forbidden:
        raise R5PersistenceError(
            "chat coordinates are reference-only; forbidden content keys: "
            + ", ".join(forbidden)
        )
    out: dict[str, str] = {}
    for raw_key, raw_value in value.items():
        key = str(raw_key)
        if not SAFE_NAME.fullmatch(key):
            raise R5PersistenceError(f"unsafe chat coordinate key: {key!r}")
        if raw_value is None:
            continue
        if isinstance(raw_value, (dict, list, tuple, set)):
            raise R5PersistenceError(
                f"chat coordinate {key!r} must be a scalar reference"
            )
        text = str(raw_value).strip()
        if text:
            out[key] = text
    if not out:
        raise R5PersistenceError("chat coordinate must contain at least one reference")
    return dict(sorted(out.items()))


def _normalise_fibre(value: Mapping[str, Any]) -> dict[str, Any]:
    if not isinstance(value, Mapping):
        raise R5PersistenceError("each fibre must be an object")
    fibre_ref = str(value.get("fibre_ref", "")).strip()
    if not fibre_ref:
        raise R5PersistenceError("fibre_ref is required")
    classification = str(value.get("classification", "")).strip()
    if classification not in EXPECTED_COUNTS:
        raise R5PersistenceError(
            f"unknown classification for {fibre_ref}: {classification!r}"
        )
    source_ast_ref = str(value.get("source_ast_ref", "")).strip()
    if not source_ast_ref:
        raise R5PersistenceError(f"source_ast_ref is required for {fibre_ref}")

    coords = [
        _normalise_coordinate(x)
        for x in (value.get("chat_coordinates") or [])
    ]
    coord_strings = sorted({_canonical_json(x) for x in coords})
    return {
        "fibre_ref": fibre_ref,
        "classification": classification,
        "source_ast_ref": source_ast_ref,
        "chat_coordinates": [json.loads(x) for x in coord_strings],
    }


def validate_manifest(value: Mapping[str, Any]) -> dict[str, Any]:
    if not isinstance(value, Mapping):
        raise R5PersistenceError("manifest must be a JSON object")
    if str(value.get("schema", "")) != SCHEMA:
        raise R5PersistenceError(f"manifest schema must be {SCHEMA}")
    if str(value.get("document_graph_ref", "")) != DOCUMENT_GRAPH_REF:
        raise R5PersistenceError(
            "manifest document_graph_ref does not match the canonical R5 graph"
        )

    fibres = [_normalise_fibre(x) for x in (value.get("fibres") or [])]
    if len(fibres) != EXPECTED_TOTAL:
        raise R5PersistenceError(
            f"expected {EXPECTED_TOTAL} fibre rows, found {len(fibres)}"
        )

    refs = [x["fibre_ref"] for x in fibres]
    if len(set(refs)) != len(refs):
        duplicates = sorted(k for k, v in Counter(refs).items() if v > 1)
        raise R5PersistenceError(
            "duplicate fibre_ref values: " + ", ".join(duplicates[:10])
        )

    counts = Counter(x["classification"] for x in fibres)
    for kind, expected in EXPECTED_COUNTS.items():
        actual = counts.get(kind, 0)
        if actual != expected:
            raise R5PersistenceError(
                f"{kind} count must be {expected}, found {actual}"
            )

    fibres.sort(key=lambda x: x["fibre_ref"])
    normalised = {
        "schema": SCHEMA,
        "document_graph_ref": DOCUMENT_GRAPH_REF,
        "fibres": fibres,
    }
    normalised["manifest_sha256"] = hashlib.sha256(
        _canonical_json(normalised).encode("utf-8")
    ).hexdigest()
    return normalised


def load_manifest(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    return validate_manifest(value)


def schema_sql() -> str:
    return """
CREATE SCHEMA IF NOT EXISTS pnf;

CREATE TABLE IF NOT EXISTS pnf.r5_formal_ast_subtraction_run (
    run_ref TEXT PRIMARY KEY,
    document_graph_ref TEXT NOT NULL,
    manifest_sha256 TEXT NOT NULL,
    discharged_core_knowledge_count INTEGER NOT NULL CHECK (discharged_core_knowledge_count = 584),
    polarity_contradiction_gap_count INTEGER NOT NULL CHECK (polarity_contradiction_gap_count = 44),
    unformalised_formal_gap_count INTEGER NOT NULL CHECK (unformalised_formal_gap_count = 58),
    total_fibre_count INTEGER NOT NULL CHECK (total_fibre_count = 686),
    chat_storage_mode TEXT NOT NULL CHECK (chat_storage_mode = 'reference-only'),
    source_schema TEXT NOT NULL,
    created_at TIMESTAMPTZ NOT NULL DEFAULT now()
);

CREATE TABLE IF NOT EXISTS pnf.r5_formal_ast_subtraction_fibre (
    run_ref TEXT NOT NULL REFERENCES pnf.r5_formal_ast_subtraction_run(run_ref) ON DELETE RESTRICT,
    fibre_ref TEXT NOT NULL,
    classification TEXT NOT NULL CHECK (
        classification IN (
            'discharged_core_knowledge',
            'polarity_contradiction_gap',
            'unformalised_formal_gap'
        )
    ),
    source_ast_ref TEXT NOT NULL,
    PRIMARY KEY (run_ref, fibre_ref)
);

CREATE TABLE IF NOT EXISTS pnf.r5_formal_ast_subtraction_chat_ref (
    run_ref TEXT NOT NULL,
    fibre_ref TEXT NOT NULL,
    coordinate_sha256 TEXT NOT NULL,
    coordinate JSONB NOT NULL,
    PRIMARY KEY (run_ref, fibre_ref, coordinate_sha256),
    FOREIGN KEY (run_ref, fibre_ref)
      REFERENCES pnf.r5_formal_ast_subtraction_fibre(run_ref, fibre_ref)
      ON DELETE RESTRICT,
    CHECK (jsonb_typeof(coordinate) = 'object'),
    CHECK (NOT (coordinate ?| ARRAY[
        'text','content','body','message','transcript','prompt','response',
        'title','summary'
    ]))
);
""".strip()


def _quote_ident(name: str) -> str:
    if not SAFE_NAME.fullmatch(name):
        raise R5PersistenceError(f"unsafe SQL identifier: {name!r}")
    return '"' + name + '"'


def _chat_table_columns(cursor: Any) -> set[str]:
    cursor.execute(
        """
        SELECT column_name
        FROM information_schema.columns
        WHERE table_schema = 'corpus'
          AND table_name = 'chat_archive_message'
        ORDER BY ordinal_position
        """
    )
    columns = {str(row[0]) for row in cursor.fetchall()}
    if not columns:
        raise R5PersistenceError(
            "required canonical table corpus.chat_archive_message is absent"
        )
    return columns


def _verify_chat_coordinate(
    cursor: Any,
    *,
    columns: set[str],
    coordinate: Mapping[str, str],
) -> None:
    usable = [(k, v) for k, v in coordinate.items() if k in columns]
    if not usable:
        raise R5PersistenceError(
            "chat coordinate has no keys present in corpus.chat_archive_message: "
            + _canonical_json(coordinate)
        )
    where = " AND ".join(f"{_quote_ident(k)} = %s" for k, _ in usable)
    params = [v for _, v in usable]
    cursor.execute(
        f"SELECT 1 FROM corpus.chat_archive_message WHERE {where} LIMIT 2",
        params,
    )
    rows = cursor.fetchall()
    if len(rows) != 1:
        raise R5PersistenceError(
            "chat coordinate must resolve to exactly one canonical archive row: "
            + _canonical_json(coordinate)
            + f" resolved={len(rows)}"
        )


def _iter_chat_refs(manifest: Mapping[str, Any]) -> Iterable[tuple[str, dict[str, str]]]:
    for fibre in manifest["fibres"]:
        for coordinate in fibre["chat_coordinates"]:
            yield str(fibre["fibre_ref"]), dict(coordinate)


def persist_manifest(
    *,
    database_url: str,
    run_ref: str,
    manifest: Mapping[str, Any],
) -> dict[str, Any]:
    try:
        import psycopg  # type: ignore
    except Exception as exc:
        raise R5PersistenceError(
            "psycopg is required for R5 PostgreSQL persistence"
        ) from exc

    if not run_ref.strip():
        raise R5PersistenceError("run_ref is required")
    validated = validate_manifest(manifest)

    with psycopg.connect(database_url) as connection:
        connection.execute("SET TRANSACTION ISOLATION LEVEL SERIALIZABLE")
        with connection.cursor() as cursor:
            cursor.execute("SELECT pg_advisory_xact_lock(hashtext(%s))", (run_ref,))
            for statement in schema_sql().split(";"):
                if statement.strip():
                    cursor.execute(statement)

            columns = _chat_table_columns(cursor)
            chat_rows = list(_iter_chat_refs(validated))
            for _, coordinate in chat_rows:
                _verify_chat_coordinate(
                    cursor,
                    columns=columns,
                    coordinate=coordinate,
                )

            cursor.execute(
                """
                SELECT manifest_sha256
                FROM pnf.r5_formal_ast_subtraction_run
                WHERE run_ref = %s
                """,
                (run_ref,),
            )
            existing = cursor.fetchone()
            if existing is not None:
                if str(existing[0]) != validated["manifest_sha256"]:
                    raise R5PersistenceError(
                        "run_ref already exists with a different manifest hash"
                    )
            else:
                cursor.execute(
                    """
                    INSERT INTO pnf.r5_formal_ast_subtraction_run (
                        run_ref,
                        document_graph_ref,
                        manifest_sha256,
                        discharged_core_knowledge_count,
                        polarity_contradiction_gap_count,
                        unformalised_formal_gap_count,
                        total_fibre_count,
                        chat_storage_mode,
                        source_schema
                    ) VALUES (%s,%s,%s,584,44,58,686,'reference-only',%s)
                    """,
                    (
                        run_ref,
                        DOCUMENT_GRAPH_REF,
                        validated["manifest_sha256"],
                        SCHEMA,
                    ),
                )

            fibre_rows = [
                (
                    run_ref,
                    f["fibre_ref"],
                    f["classification"],
                    f["source_ast_ref"],
                )
                for f in validated["fibres"]
            ]
            cursor.executemany(
                """
                INSERT INTO pnf.r5_formal_ast_subtraction_fibre
                    (run_ref, fibre_ref, classification, source_ast_ref)
                VALUES (%s,%s,%s,%s)
                ON CONFLICT (run_ref, fibre_ref) DO NOTHING
                """,
                fibre_rows,
            )

            reference_rows = []
            for fibre_ref, coordinate in chat_rows:
                encoded = _canonical_json(coordinate)
                reference_rows.append(
                    (
                        run_ref,
                        fibre_ref,
                        hashlib.sha256(encoded.encode("utf-8")).hexdigest(),
                        encoded,
                    )
                )
            if reference_rows:
                cursor.executemany(
                    """
                    INSERT INTO pnf.r5_formal_ast_subtraction_chat_ref
                        (run_ref, fibre_ref, coordinate_sha256, coordinate)
                    VALUES (%s,%s,%s,%s::jsonb)
                    ON CONFLICT (run_ref, fibre_ref, coordinate_sha256) DO NOTHING
                    """,
                    reference_rows,
                )

            cursor.execute(
                """
                SELECT classification, count(*)
                FROM pnf.r5_formal_ast_subtraction_fibre
                WHERE run_ref = %s
                GROUP BY classification
                """,
                (run_ref,),
            )
            persisted_counts = {str(k): int(v) for k, v in cursor.fetchall()}
            if persisted_counts != EXPECTED_COUNTS:
                raise R5PersistenceError(
                    "post-write partition verification failed: "
                    + _canonical_json(persisted_counts)
                )

            cursor.execute(
                """
                SELECT count(*)
                FROM pnf.r5_formal_ast_subtraction_chat_ref
                WHERE run_ref = %s
                """,
                (run_ref,),
            )
            persisted_chat_refs = int(cursor.fetchone()[0])
            if persisted_chat_refs != len(reference_rows):
                raise R5PersistenceError(
                    "post-write chat reference count mismatch: "
                    f"expected={len(reference_rows)} actual={persisted_chat_refs}"
                )

        connection.commit()

    return {
        "schema": SCHEMA,
        "run_ref": run_ref,
        "document_graph_ref": DOCUMENT_GRAPH_REF,
        "manifest_sha256": validated["manifest_sha256"],
        "partition": dict(EXPECTED_COUNTS),
        "total_fibres": EXPECTED_TOTAL,
        "chat_reference_count": len(list(_iter_chat_refs(validated))),
        "chat_storage_mode": "reference-only",
        "single_postgresql_transaction": True,
        "database_url_emitted": False,
        "semantic_promotion": False,
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Persist Stage R5 formal-AST subtraction into PostgreSQL."
    )
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument(
        "--run-ref",
        default="ao.fleet.dynamic.27dfb71b9cdf",
    )
    parser.add_argument(
        "--database-url",
        default=os.environ.get("DATABASE_URL", ""),
    )
    parser.add_argument("--verify-only", action="store_true")
    parser.add_argument("--receipt", type=Path)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    manifest = load_manifest(args.manifest)

    if args.verify_only:
        receipt = {
            "schema": SCHEMA,
            "run_ref": args.run_ref,
            "document_graph_ref": DOCUMENT_GRAPH_REF,
            "manifest_sha256": manifest["manifest_sha256"],
            "partition": dict(EXPECTED_COUNTS),
            "total_fibres": EXPECTED_TOTAL,
            "chat_reference_count": len(list(_iter_chat_refs(manifest))),
            "chat_storage_mode": "reference-only",
            "database_persisted": False,
            "semantic_promotion": False,
        }
    else:
        if not args.database_url:
            raise R5PersistenceError(
                "DATABASE_URL or --database-url is required unless --verify-only is used"
            )
        receipt = persist_manifest(
            database_url=args.database_url,
            run_ref=args.run_ref,
            manifest=manifest,
        )
        receipt["database_persisted"] = True

    output = json.dumps(receipt, indent=2, sort_keys=True) + "\n"
    if args.receipt:
        args.receipt.parent.mkdir(parents=True, exist_ok=True)
        args.receipt.write_text(output, encoding="utf-8")
    print(output, end="")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except R5PersistenceError as exc:
        print(f"R5_PERSISTENCE_ERROR {exc}", file=sys.stderr)
        raise SystemExit(2)
