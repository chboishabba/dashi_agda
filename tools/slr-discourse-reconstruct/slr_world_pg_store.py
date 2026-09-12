#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import sys
from typing import Any, Iterable, Mapping, Sequence

SCHEMA = "slr-world-postgres-store-v1"


def schema_sql() -> str:
    return """
CREATE TABLE IF NOT EXISTS slr_world_source_manifestation (
    source_manifestation_id TEXT PRIMARY KEY,
    source_kind TEXT NOT NULL,
    qid TEXT NOT NULL DEFAULT '',
    language TEXT NOT NULL DEFAULT '',
    revision_ref TEXT NOT NULL DEFAULT '',
    source_text_sha256 TEXT NOT NULL DEFAULT '',
    payload JSONB NOT NULL,
    created_at TIMESTAMPTZ NOT NULL DEFAULT now()
);
CREATE TABLE IF NOT EXISTS slr_world_pnf_candidate (
    claim_candidate_id TEXT PRIMARY KEY,
    source_manifestation_id TEXT NOT NULL,
    payload JSONB NOT NULL,
    created_at TIMESTAMPTZ NOT NULL DEFAULT now()
);
CREATE TABLE IF NOT EXISTS slr_world_atom (
    atom_id TEXT PRIMARY KEY,
    atom_kind TEXT NOT NULL,
    subject_qid TEXT NOT NULL DEFAULT '',
    source_manifestation_id TEXT NOT NULL DEFAULT '',
    payload JSONB NOT NULL,
    created_at TIMESTAMPTZ NOT NULL DEFAULT now()
);
CREATE TABLE IF NOT EXISTS slr_world_gap (
    gap_id TEXT NOT NULL,
    iteration_index INTEGER NOT NULL,
    surface_id TEXT NOT NULL DEFAULT '',
    payload JSONB NOT NULL,
    created_at TIMESTAMPTZ NOT NULL DEFAULT now(),
    PRIMARY KEY (gap_id, iteration_index)
);
CREATE TABLE IF NOT EXISTS slr_world_obligation (
    obligation_id TEXT NOT NULL,
    iteration_index INTEGER NOT NULL,
    obligation_kind TEXT NOT NULL,
    payload JSONB NOT NULL,
    created_at TIMESTAMPTZ NOT NULL DEFAULT now(),
    PRIMARY KEY (obligation_id, iteration_index)
);
CREATE TABLE IF NOT EXISTS slr_world_route_action (
    action_id TEXT NOT NULL,
    iteration_index INTEGER NOT NULL,
    payload JSONB NOT NULL,
    created_at TIMESTAMPTZ NOT NULL DEFAULT now(),
    PRIMARY KEY (action_id, iteration_index)
);
CREATE TABLE IF NOT EXISTS slr_world_iteration (
    iteration_index INTEGER PRIMARY KEY,
    parent_iteration_index INTEGER,
    payload JSONB NOT NULL,
    created_at TIMESTAMPTZ NOT NULL DEFAULT now()
);
""".strip()


def _json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def _stable_id(prefix: str, value: Any) -> str:
    return prefix + hashlib.sha256(_json(value).encode("utf-8")).hexdigest()


def persist_rows(
    cursor: Any,
    *,
    source_manifestations: Iterable[Mapping[str, Any]] = (),
    pnf_candidates: Iterable[Mapping[str, Any]] = (),
    world_atoms: Iterable[Mapping[str, Any]] = (),
    gaps: Iterable[Mapping[str, Any]] = (),
    obligations: Iterable[Mapping[str, Any]] = (),
    route_actions: Iterable[Mapping[str, Any]] = (),
    iteration_rows: Iterable[Mapping[str, Any]] = (),
) -> None:
    """Small/debug fallback. Production persistence uses bulk_persist_rows."""
    source_rows = [
        (
            str(r["source_manifestation_id"]), str(r.get("source_kind", "")),
            str(r.get("qid", "")), str(r.get("language", "")),
            str(r.get("revision_ref", "")), str(r.get("source_text_sha256", "")),
            _json(r.get("payload") or {}),
        )
        for r in source_manifestations
    ]
    if source_rows:
        cursor.executemany(
            """
            INSERT INTO slr_world_source_manifestation
              (source_manifestation_id, source_kind, qid, language, revision_ref, source_text_sha256, payload)
            VALUES (%s,%s,%s,%s,%s,%s,%s::jsonb)
            ON CONFLICT (source_manifestation_id) DO NOTHING
            """,
            source_rows,
        )
    pnf_rows = [
        (str(r["claim_candidate_id"]), str(r["source_manifestation_id"]), _json(r.get("payload") or {}))
        for r in pnf_candidates
    ]
    if pnf_rows:
        cursor.executemany(
            """
            INSERT INTO slr_world_pnf_candidate (claim_candidate_id, source_manifestation_id, payload)
            VALUES (%s,%s,%s::jsonb)
            ON CONFLICT (claim_candidate_id) DO NOTHING
            """,
            pnf_rows,
        )
    atom_rows = [
        (
            str(r["atom_id"]), str(r.get("atom_kind", "")), str(r.get("subject_qid", "")),
            str(r.get("source_manifestation_id", "")), _json(r.get("payload") or {}),
        )
        for r in world_atoms
    ]
    if atom_rows:
        cursor.executemany(
            """
            INSERT INTO slr_world_atom (atom_id, atom_kind, subject_qid, source_manifestation_id, payload)
            VALUES (%s,%s,%s,%s,%s::jsonb)
            ON CONFLICT (atom_id) DO NOTHING
            """,
            atom_rows,
        )
    gap_rows = [
        (str(r["gap_id"]), int(r["iteration_index"]), str(r.get("surface_id", "")), _json(r.get("payload") or {}))
        for r in gaps
    ]
    if gap_rows:
        cursor.executemany(
            """
            INSERT INTO slr_world_gap (gap_id, iteration_index, surface_id, payload)
            VALUES (%s,%s,%s,%s::jsonb)
            ON CONFLICT (gap_id, iteration_index) DO NOTHING
            """,
            gap_rows,
        )
    obligation_rows = [
        (str(r["obligation_id"]), int(r["iteration_index"]), str(r.get("obligation_kind", "")), _json(r.get("payload") or {}))
        for r in obligations
    ]
    if obligation_rows:
        cursor.executemany(
            """
            INSERT INTO slr_world_obligation (obligation_id, iteration_index, obligation_kind, payload)
            VALUES (%s,%s,%s,%s::jsonb)
            ON CONFLICT (obligation_id, iteration_index) DO NOTHING
            """,
            obligation_rows,
        )
    route_rows = [
        (str(r["action_id"]), int(r["iteration_index"]), _json(r.get("payload") or {}))
        for r in route_actions
    ]
    if route_rows:
        cursor.executemany(
            """
            INSERT INTO slr_world_route_action (action_id, iteration_index, payload)
            VALUES (%s,%s,%s::jsonb)
            ON CONFLICT (action_id, iteration_index) DO NOTHING
            """,
            route_rows,
        )
    iteration_payloads = [
        (int(r["iteration_index"]), r.get("parent_iteration_index"), _json(r.get("payload") or {}))
        for r in iteration_rows
    ]
    if iteration_payloads:
        cursor.executemany(
            """
            INSERT INTO slr_world_iteration (iteration_index, parent_iteration_index, payload)
            VALUES (%s,%s,%s::jsonb)
            ON CONFLICT (iteration_index) DO NOTHING
            """,
            iteration_payloads,
        )


def _copy_stage(
    cursor: Any,
    *,
    stage_table: str,
    target_table: str,
    stage_columns: Sequence[tuple[str, str]],
    target_columns: Sequence[str],
    select_expressions: Sequence[str],
    conflict_columns: Sequence[str],
    rows: Sequence[tuple[Any, ...]],
) -> None:
    if not rows:
        return
    definitions = ", ".join(f"{name} {kind}" for name, kind in stage_columns)
    stage_names = ", ".join(name for name, _ in stage_columns)
    target_names = ", ".join(target_columns)
    selects = ", ".join(select_expressions)
    conflicts = ", ".join(conflict_columns)
    cursor.execute(f"CREATE TEMP TABLE {stage_table} ({definitions}) ON COMMIT DROP")
    with cursor.copy(f"COPY {stage_table} ({stage_names}) FROM STDIN") as copy:
        for row in rows:
            copy.write_row(row)
    cursor.execute(
        f"INSERT INTO {target_table} ({target_names}) "
        f"SELECT {selects} FROM {stage_table} "
        f"ON CONFLICT ({conflicts}) DO NOTHING"
    )


def bulk_persist_rows(
    cursor: Any,
    *,
    source_manifestations: Iterable[Mapping[str, Any]] = (),
    pnf_candidates: Iterable[Mapping[str, Any]] = (),
    world_atoms: Iterable[Mapping[str, Any]] = (),
    gaps: Iterable[Mapping[str, Any]] = (),
    obligations: Iterable[Mapping[str, Any]] = (),
    route_actions: Iterable[Mapping[str, Any]] = (),
    iteration_rows: Iterable[Mapping[str, Any]] = (),
) -> None:
    """COPY rows into transaction-local staging tables, then idempotently merge."""
    source_rows = [
        (
            str(r["source_manifestation_id"]), str(r.get("source_kind", "")),
            str(r.get("qid", "")), str(r.get("language", "")),
            str(r.get("revision_ref", "")), str(r.get("source_text_sha256", "")),
            _json(r.get("payload") or {}),
        )
        for r in source_manifestations
    ]
    _copy_stage(
        cursor,
        stage_table="slr_stage_source_manifestation",
        target_table="slr_world_source_manifestation",
        stage_columns=(("source_manifestation_id", "TEXT"), ("source_kind", "TEXT"), ("qid", "TEXT"),
                       ("language", "TEXT"), ("revision_ref", "TEXT"), ("source_text_sha256", "TEXT"),
                       ("payload_text", "TEXT")),
        target_columns=("source_manifestation_id", "source_kind", "qid", "language", "revision_ref", "source_text_sha256", "payload"),
        select_expressions=("source_manifestation_id", "source_kind", "qid", "language", "revision_ref", "source_text_sha256", "payload_text::jsonb"),
        conflict_columns=("source_manifestation_id",),
        rows=source_rows,
    )

    pnf_rows = [
        (str(r["claim_candidate_id"]), str(r["source_manifestation_id"]), _json(r.get("payload") or {}))
        for r in pnf_candidates
    ]
    _copy_stage(
        cursor,
        stage_table="slr_stage_pnf_candidate",
        target_table="slr_world_pnf_candidate",
        stage_columns=(("claim_candidate_id", "TEXT"), ("source_manifestation_id", "TEXT"), ("payload_text", "TEXT")),
        target_columns=("claim_candidate_id", "source_manifestation_id", "payload"),
        select_expressions=("claim_candidate_id", "source_manifestation_id", "payload_text::jsonb"),
        conflict_columns=("claim_candidate_id",),
        rows=pnf_rows,
    )

    atom_rows = [
        (
            str(r["atom_id"]), str(r.get("atom_kind", "")), str(r.get("subject_qid", "")),
            str(r.get("source_manifestation_id", "")), _json(r.get("payload") or {}),
        )
        for r in world_atoms
    ]
    _copy_stage(
        cursor,
        stage_table="slr_stage_world_atom",
        target_table="slr_world_atom",
        stage_columns=(("atom_id", "TEXT"), ("atom_kind", "TEXT"), ("subject_qid", "TEXT"),
                       ("source_manifestation_id", "TEXT"), ("payload_text", "TEXT")),
        target_columns=("atom_id", "atom_kind", "subject_qid", "source_manifestation_id", "payload"),
        select_expressions=("atom_id", "atom_kind", "subject_qid", "source_manifestation_id", "payload_text::jsonb"),
        conflict_columns=("atom_id",),
        rows=atom_rows,
    )

    gap_rows = [
        (str(r["gap_id"]), int(r["iteration_index"]), str(r.get("surface_id", "")), _json(r.get("payload") or {}))
        for r in gaps
    ]
    _copy_stage(
        cursor,
        stage_table="slr_stage_world_gap",
        target_table="slr_world_gap",
        stage_columns=(("gap_id", "TEXT"), ("iteration_index", "INTEGER"), ("surface_id", "TEXT"), ("payload_text", "TEXT")),
        target_columns=("gap_id", "iteration_index", "surface_id", "payload"),
        select_expressions=("gap_id", "iteration_index", "surface_id", "payload_text::jsonb"),
        conflict_columns=("gap_id", "iteration_index"),
        rows=gap_rows,
    )

    obligation_rows = [
        (str(r["obligation_id"]), int(r["iteration_index"]), str(r.get("obligation_kind", "")), _json(r.get("payload") or {}))
        for r in obligations
    ]
    _copy_stage(
        cursor,
        stage_table="slr_stage_world_obligation",
        target_table="slr_world_obligation",
        stage_columns=(("obligation_id", "TEXT"), ("iteration_index", "INTEGER"), ("obligation_kind", "TEXT"), ("payload_text", "TEXT")),
        target_columns=("obligation_id", "iteration_index", "obligation_kind", "payload"),
        select_expressions=("obligation_id", "iteration_index", "obligation_kind", "payload_text::jsonb"),
        conflict_columns=("obligation_id", "iteration_index"),
        rows=obligation_rows,
    )

    route_rows = [
        (str(r["action_id"]), int(r["iteration_index"]), _json(r.get("payload") or {}))
        for r in route_actions
    ]
    _copy_stage(
        cursor,
        stage_table="slr_stage_world_route_action",
        target_table="slr_world_route_action",
        stage_columns=(("action_id", "TEXT"), ("iteration_index", "INTEGER"), ("payload_text", "TEXT")),
        target_columns=("action_id", "iteration_index", "payload"),
        select_expressions=("action_id", "iteration_index", "payload_text::jsonb"),
        conflict_columns=("action_id", "iteration_index"),
        rows=route_rows,
    )

    iteration_payloads = [
        (int(r["iteration_index"]), r.get("parent_iteration_index"), _json(r.get("payload") or {}))
        for r in iteration_rows
    ]
    _copy_stage(
        cursor,
        stage_table="slr_stage_world_iteration",
        target_table="slr_world_iteration",
        stage_columns=(("iteration_index", "INTEGER"), ("parent_iteration_index", "INTEGER"), ("payload_text", "TEXT")),
        target_columns=("iteration_index", "parent_iteration_index", "payload"),
        select_expressions=("iteration_index", "parent_iteration_index", "payload_text::jsonb"),
        conflict_columns=("iteration_index",),
        rows=iteration_payloads,
    )


def _parse_env_file(path: Path) -> dict[str, str]:
    out: dict[str, str] = {}
    if not path.exists():
        return out
    for raw in path.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if not line or line.startswith("#") or "=" not in line:
            continue
        key, value = line.split("=", 1)
        value = value.strip().strip("\"").strip("'")
        out[key.strip()] = value
    return out


def database_url(*, env_file: Path | None = None) -> str:
    value = os.environ.get("DATABASE_URL", "").strip()
    if value:
        return value
    if env_file is not None:
        value = _parse_env_file(env_file).get("DATABASE_URL", "").strip()
    if not value:
        raise RuntimeError("DATABASE_URL is required for SLR Postgres persistence")
    return value


def persistence_receipt(*, database_url: str, source_manifestations: int, pnf_candidates: int,
                        world_atoms: int, gaps: int, obligations: int,
                        route_actions: int, iteration_rows: int,
                        persistence_mode: str = "copy-staging") -> dict[str, Any]:
    _ = database_url
    return {
        "schema": SCHEMA,
        "database_config_source": "DATABASE_URL",
        "persistence_mode": persistence_mode,
        "source_manifestations": int(source_manifestations),
        "pnf_candidates": int(pnf_candidates),
        "world_atoms": int(world_atoms),
        "gaps": int(gaps),
        "obligations": int(obligations),
        "route_actions": int(route_actions),
        "iteration_rows": int(iteration_rows),
        "append_only_identity_keys": True,
        "idempotent_conflict_safe_writes": True,
        "conflicting_replay_rewrites_prior_evidence": False,
        "copy_staging_bulk_path": persistence_mode == "copy-staging",
        "database_url_emitted": False,
        "postgres_persistence_is_semantic_authority": False,
        "candidate_only": True,
        "semantic_promotion": False,
    }


def _load(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise RuntimeError(f"expected JSON object: {path}")
    return value


def rows_from_round(article: dict[str, Any], closure: dict[str, Any], route_plan: dict[str, Any],
                    iteration: dict[str, Any]) -> dict[str, list[dict[str, Any]]]:
    manifestations: list[dict[str, Any]] = []
    for m in article.get("article_manifestations") or article.get("manifestations") or []:
        if not isinstance(m, dict):
            continue
        qid = str(m.get("qid", "")); lang = str(m.get("language", "")); rev = str(m.get("revision_id", ""))
        sid = str(m.get("document_ref", "")) or (f"wiki:{qid}:{lang}:{rev}" if qid and lang and rev else "")
        if not sid:
            continue
        manifestations.append({
            "source_manifestation_id": sid,
            "source_kind": str(m.get("manifestation_kind", "wikipedia-revision-text")),
            "qid": qid,
            "language": lang,
            "revision_ref": rev or str(m.get("revision_ref", "")),
            "source_text_sha256": str(m.get("source_text_sha256", "")),
            "payload": m,
        })
    pnf_rows: list[dict[str, Any]] = []
    for c in article.get("pnf_candidates") or []:
        if not isinstance(c, dict) or not c.get("claim_candidate_id"):
            continue
        pnf_rows.append({
            "claim_candidate_id": str(c["claim_candidate_id"]),
            "source_manifestation_id": str(c.get("document_ref", "")),
            "payload": c,
        })
    atom_rows: list[dict[str, Any]] = []
    for a in closure.get("canonical_atoms") or []:
        if not isinstance(a, dict) or not a.get("atom_id"):
            continue
        atom_rows.append({
            "atom_id": str(a["atom_id"]),
            "atom_kind": str(a.get("kind", "")),
            "subject_qid": str(a.get("subject_qid", "")),
            "source_manifestation_id": str(a.get("document_ref", "")),
            "payload": a,
        })
    idx = int(iteration.get("iteration_index", 0) or 0)
    gap_rows: list[dict[str, Any]] = []
    for gap in closure.get("gaps") or []:
        if not isinstance(gap, dict):
            continue
        sid = str(gap.get("surface_id", ""))
        missing = [str(x) for x in gap.get("missing_atom_ids") or [] if str(x)]
        if missing:
            for atom_id in missing:
                gap_rows.append({
                    "gap_id": f"gap:{sid}:{atom_id}",
                    "iteration_index": idx,
                    "surface_id": sid,
                    "payload": {**gap, "missing_atom_id": atom_id},
                })
        elif str(gap.get("gap_kind", "")) == "missing-surface":
            gap_rows.append({
                "gap_id": f"gap:{sid}:missing-surface",
                "iteration_index": idx,
                "surface_id": sid,
                "payload": gap,
            })
    obligation_rows: list[dict[str, Any]] = []
    for obligation in closure.get("acquisition_obligations") or []:
        if not isinstance(obligation, dict):
            continue
        oid = str(obligation.get("obligation_id", "")) or _stable_id("obligation:", obligation)
        obligation_rows.append({
            "obligation_id": oid,
            "iteration_index": idx,
            "obligation_kind": str(obligation.get("obligation_kind", "")),
            "payload": obligation,
        })
    route_rows = [
        {"action_id": str(a.get("action_id", "")), "iteration_index": idx, "payload": a}
        for a in route_plan.get("selected_route_actions") or []
        if isinstance(a, dict) and a.get("action_id")
    ]
    iteration_rows = [{
        "iteration_index": idx,
        "parent_iteration_index": idx - 1 if idx > 0 else None,
        "payload": iteration,
    }]
    return {
        "source_manifestations": manifestations,
        "pnf_candidates": pnf_rows,
        "world_atoms": atom_rows,
        "gaps": gap_rows,
        "obligations": obligation_rows,
        "route_actions": route_rows,
        "iteration_rows": iteration_rows,
    }


def persist_round(*, article_path: Path, closure_path: Path, route_plan_path: Path,
                  iteration_path: Path, env_file: Path | None, receipt_path: Path,
                  persistence_mode: str = "copy-staging") -> dict[str, Any]:
    try:
        import psycopg  # type: ignore
    except Exception as exc:
        raise RuntimeError("psycopg is required for SLR Postgres persistence") from exc
    url = database_url(env_file=env_file)
    rows = rows_from_round(_load(article_path), _load(closure_path), _load(route_plan_path), _load(iteration_path))
    with psycopg.connect(url) as connection:
        with connection.cursor() as cursor:
            for statement in schema_sql().split(";"):
                if statement.strip():
                    cursor.execute(statement)
            if persistence_mode == "rowwise-debug":
                persist_rows(cursor, **rows)
            elif persistence_mode == "copy-staging":
                bulk_persist_rows(cursor, **rows)
            else:
                raise RuntimeError(f"unsupported persistence mode: {persistence_mode}")
        connection.commit()
    receipt = persistence_receipt(
        database_url=url,
        source_manifestations=len(rows["source_manifestations"]),
        pnf_candidates=len(rows["pnf_candidates"]),
        world_atoms=len(rows["world_atoms"]),
        gaps=len(rows["gaps"]),
        obligations=len(rows["obligations"]),
        route_actions=len(rows["route_actions"]),
        iteration_rows=len(rows["iteration_rows"]),
        persistence_mode=persistence_mode,
    )
    receipt_path.parent.mkdir(parents=True, exist_ok=True)
    receipt_path.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return receipt


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser()
    sub = p.add_subparsers(dest="command", required=True)
    s = sub.add_parser("schema")
    s.add_argument("--output", type=Path)
    r = sub.add_parser("persist-round")
    r.add_argument("--article-pnf", type=Path, required=True)
    r.add_argument("--closure", type=Path, required=True)
    r.add_argument("--route-plan", type=Path, required=True)
    r.add_argument("--iteration", type=Path, required=True)
    r.add_argument("--env-file", type=Path, default=Path(".env"))
    r.add_argument("--receipt", type=Path, required=True)
    r.add_argument("--persistence-mode", choices=("copy-staging", "rowwise-debug"), default="copy-staging")
    return p.parse_args()


def main() -> int:
    args = parse_args()
    if args.command == "schema":
        text = schema_sql() + "\n"
        if args.output:
            args.output.write_text(text, encoding="utf-8")
        else:
            print(text, end="")
        return 0
    receipt = persist_round(
        article_path=args.article_pnf,
        closure_path=args.closure,
        route_plan_path=args.route_plan,
        iteration_path=args.iteration,
        env_file=args.env_file,
        receipt_path=args.receipt,
        persistence_mode=args.persistence_mode,
    )
    print(
        "SLR_WORLD_POSTGRES_PERSISTENCE_RECEIPT "
        f"schema={SCHEMA} persistence_mode={receipt['persistence_mode']} "
        f"source_manifestations={receipt['source_manifestations']} "
        f"pnf_candidates={receipt['pnf_candidates']} world_atoms={receipt['world_atoms']} "
        f"gaps={receipt['gaps']} obligations={receipt['obligations']} "
        f"route_actions={receipt['route_actions']} iteration_rows={receipt['iteration_rows']} "
        "copy_staging_bulk_path=true database_url_emitted=false "
        "conflicting_replay_rewrites_prior_evidence=false "
        "postgres_persistence_is_semantic_authority=false candidate_only=true semantic_promotion=false",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
