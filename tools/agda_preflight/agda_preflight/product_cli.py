from __future__ import annotations

import argparse
from pathlib import Path
import sqlite3
import sys

from .development_history import NarrativeEvent
from .external_proof_bridge import ExternalProofDemand, ExternalProofRouter
from .proof_router import ProofRouteRequest, ProofRouter, ensure_proof_router_schema
from .repository_annotations import (
    capture_repository_annotations,
    restore_repository_annotations,
)
from .repository_cli import main as repository_main
from .repository_coverage import repository_inventory_coverage
from .repository_git_store import git_history_status, replace_git_history
from .repository_inventory import refresh_repository_inventory
from .repository_store import (
    DEFAULT_REPOSITORY_DB,
    ensure_repository_schema,
    load_narrative_events,
    narrative_coverage,
)
from .service import DashiAgdaService


def _connect(root: Path, database: Path) -> sqlite3.Connection:
    path = database if database.is_absolute() else root / database
    path.parent.mkdir(parents=True, exist_ok=True)
    conn = sqlite3.connect(path)
    conn.row_factory = sqlite3.Row
    conn.execute("PRAGMA journal_mode=WAL")
    conn.execute("PRAGMA synchronous=NORMAL")
    conn.execute("PRAGMA foreign_keys=ON")
    conn.execute("PRAGMA busy_timeout=5000")
    ensure_repository_schema(conn)
    ensure_proof_router_schema(conn)
    return conn


def _common(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--database", type=Path, default=DEFAULT_REPOSITORY_DB)


def _status(argv) -> int:
    parser = argparse.ArgumentParser(
        prog="dashi-repo status",
        description="Report coverage of the unified repository-intelligence database.",
    )
    _common(parser)
    args = parser.parse_args(argv)
    root = args.root.resolve()
    database = args.database if args.database.is_absolute() else root / args.database
    with _connect(root, args.database) as conn:
        semantic = repository_inventory_coverage(root, conn)
        narrative = narrative_coverage(conn)
        git = git_history_status(conn)
        counts = {}
        for table in (
            "modules",
            "repo_files",
            "repo_symbols",
            "repo_symbol_signatures",
            "narrative_events",
            "pull_requests",
            "git_commits",
            "git_commit_parents",
            "git_refs",
            "promotion_receipts",
            "da51_objects",
            "da51_symbol_links",
            "da51_evidence",
            "proof_routes",
            "proof_route_matches",
            "external_proof_demands",
            "external_formal_evidence",
        ):
            try:
                counts[table] = int(
                    conn.execute(f"SELECT count(*) FROM {table}").fetchone()[0]
                )
            except sqlite3.DatabaseError:
                counts[table] = 0
    print(f"database\t{database}")
    print(f"semantic_available\t{semantic.get('available', False)}")
    print(f"semantic_complete\t{semantic.get('complete', False)}")
    print(f"semantic_producer\t{semantic.get('producer')}")
    print(f"semantic_missing\t{len(semantic.get('missing', ()))}")
    print(f"semantic_stale\t{len(semantic.get('stale', ()))}")
    print(f"semantic_parse_errors\t{len(semantic.get('parse_errors', ()))}")
    print(f"narrative_available\t{narrative.get('available', False)}")
    print(f"narrative_complete\t{narrative.get('complete', False)}")
    print(f"git_complete\t{git.get('complete', False)}")
    for key in ("commits", "parent_edges", "refs", "commit_paths"):
        print(f"git_{key}\t{git[key]}")
    for table, count in counts.items():
        print(f"table_{table}\t{count}")
    return 0


def _index(argv) -> int:
    parser = argparse.ArgumentParser(
        prog="dashi-repo index",
        description="Build the canonical whole-repo inventory with the preflight parser.",
    )
    _common(parser)
    args = parser.parse_args(argv)
    root = args.root.resolve()
    with _connect(root, args.database) as conn:
        annotations = capture_repository_annotations(conn)
        result = refresh_repository_inventory(root, conn)
        result["annotations_restored"] = restore_repository_annotations(
            conn,
            annotations,
        )
    database = args.database if args.database.is_absolute() else root / args.database
    print(f"database\t{database}")
    for key in (
        "files",
        "symbols",
        "imports",
        "parse_errors",
        "annotations_restored",
        "elapsed_ms",
    ):
        print(f"{key}\t{result[key]}")
    for error in result["errors"]:
        print(f"parse_error\t{error['path']}\t{error['error']}")
    return 0 if not result["parse_errors"] else 2


def _harvest(argv) -> int:
    parser = argparse.ArgumentParser(
        prog="dashi-repo harvest",
        description="Persist Git/PR development history into the shared DB.",
    )
    _common(parser)
    parser.add_argument("--github-prs")
    parser.add_argument("--max-commits", type=int)
    args = parser.parse_args(argv)
    root = args.root.resolve()
    forwarded = ["harvest", "--root", str(root), "--database", str(args.database)]
    if args.github_prs:
        forwarded.extend(["--github-prs", args.github_prs])
    if args.max_commits is not None:
        forwarded.extend(["--max-commits", str(args.max_commits)])
    history_code = repository_main(forwarded)
    complete = args.max_commits is None
    with _connect(root, args.database) as conn:
        events = [NarrativeEvent.from_record(item) for item in load_narrative_events(conn)]
        git_result = replace_git_history(conn, root, events, complete=complete)
    for key in ("commits", "parent_edges", "refs", "commit_paths", "complete"):
        print(f"git_{key}\t{git_result[key]}")
    return history_code


def _bootstrap(argv) -> int:
    parser = argparse.ArgumentParser(
        prog="dashi-repo bootstrap",
        description="Build semantic inventory then harvest complete Git/PR history into one DB.",
    )
    _common(parser)
    parser.add_argument("--github-prs")
    args = parser.parse_args(argv)
    root = args.root.resolve()
    index_code = _index(["--root", str(root), "--database", str(args.database)])
    forwarded = ["--root", str(root), "--database", str(args.database)]
    if args.github_prs:
        forwarded.extend(["--github-prs", args.github_prs])
    history_code = _harvest(forwarded)
    return max(index_code, history_code)


def _print_scalar(prefix: str, item) -> None:
    if isinstance(item, bool):
        print(f"{prefix}\t{item}")
    elif item is None or isinstance(item, (str, int, float)):
        print(f"{prefix}\t{item}")


def _da51(argv) -> int:
    parser = argparse.ArgumentParser(
        prog="dashi-repo da51",
        description="Resolve and attach authority-neutral DA51 identity/provenance.",
    )
    sub = parser.add_subparsers(dest="action", required=True)
    resolve = sub.add_parser("resolve")
    resolve.add_argument("address")
    _common(resolve)
    link = sub.add_parser("link")
    link.add_argument("address")
    link.add_argument("symbol")
    link.add_argument("--relation", required=True)
    link.add_argument("--source", required=True)
    _common(link)
    add = sub.add_parser("add-evidence")
    add.add_argument("address")
    add.add_argument("--producer", required=True)
    add.add_argument("--artifact", required=True)
    add.add_argument("--kind", required=True)
    add.add_argument("--revision", default="")
    add.add_argument("--digest", default="")
    _common(add)
    evidence = sub.add_parser("evidence")
    evidence.add_argument("address")
    _common(evidence)
    frontier = sub.add_parser("frontier")
    frontier.add_argument("address")
    _common(frontier)
    args = parser.parse_args(argv)
    root = args.root.resolve()
    with _connect(root, args.database) as conn:
        router = ProofRouter(
            discovery=lambda query, **kwargs: {
                "query": query,
                "absence_claim_permitted": False,
                "absence_status": "not-requested",
            },
            connection=conn,
        )
        if args.action == "resolve":
            result = router.resolve_da51(args.address)
            for key in ("address", "type_code", "data_hex", "authority"):
                _print_scalar(key, result.get(key))
            atlas = result.get("atlas")
            if atlas:
                for key in ("level", "biome", "status", "serial", "reserved"):
                    _print_scalar(f"atlas_{key}", atlas[key])
            for item in result.get("symbol_links", ()):
                print(f"symbol_link\t{item['symbol_id']}\t{item['relation']}\t{item['source']}")
            for item in result.get("evidence", ()):
                print("evidence\t{}\t{}\t{}\t{}\t{}".format(item["producer"], item["evidence_kind"], item["artifact"], item["revision"], item["digest"]))
            return 0
        if args.action == "link":
            result = router.link_da51(args.address, args.symbol, relation=args.relation, source=args.source)
            print(f"address\t{result['address']}")
            print(f"symbol_links\t{len(result['symbol_links'])}")
            return 0
        if args.action == "add-evidence":
            result = router.add_evidence(args.address, producer=args.producer, artifact=args.artifact, evidence_kind=args.kind, revision=args.revision, digest=args.digest)
            print(f"address\t{result['address']}")
            print(f"evidence_count\t{len(result['evidence'])}")
            print(f"authority\t{result['authority']}")
            return 0
        if args.action == "evidence":
            result = router.resolve_da51(args.address)
            print(f"address\t{result['address']}")
            for item in result["evidence"]:
                print("evidence\t{}\t{}\t{}\t{}\t{}\t{}".format(item["producer"], item["evidence_kind"], item["artifact"], item["revision"], item["digest"], item["authority"]))
            return 0
        if args.action == "frontier":
            result = router.frontier_for(args.address)
            print(f"address\t{result['address']}")
            print(f"authority\t{result['authority']}")
            for item in result["routes"]:
                print("route\t{}\t{}\t{}\t{}\t{}".format(item["route_id"], item["debt_kind"], item["recommended_backend"], item["absence_status"], bool(item["generation_permitted"])))
            return 0
    raise AssertionError(args.action)


def _add_route_options(route: argparse.ArgumentParser) -> None:
    route.add_argument("query")
    route.add_argument("--target-prover", choices=("lean", "agda"), default="lean")
    route.add_argument("--claim-kind", choices=("deductive", "empirical"), default="deductive")
    route.add_argument("--mathematical-status", choices=("novel-open", "source-established", "derived-in-repo", "experimentally-supported"), default="novel-open")
    route.add_argument("--statement-status", choices=("not-transcribed", "transcribed-unaligned", "source-aligned"), default="not-transcribed")
    route.add_argument("--certification-status", choices=("uncertified", "proof-deferred", "lean-kernel", "agda-kernel"), default="uncertified")
    route.add_argument("--da51")
    route.add_argument("--source-declaration")
    route.add_argument("--current-source-hash")
    route.add_argument("--semantic-catalog", type=Path)
    route.add_argument("--limit", type=int, default=50)
    _common(route)


def _service_route(args, root: Path, *, external: bool):
    database = args.database if args.database.is_absolute() else root / args.database
    semantic_catalog = args.semantic_catalog
    if semantic_catalog is not None and not semantic_catalog.is_absolute():
        semantic_catalog = root / semantic_catalog
    with DashiAgdaService(root, database, semantic_catalog=semantic_catalog) as service:
        router = ProofRouter(discovery=service.discover, semantic_catalog=service.semantic, connection=service.index.connection)
        if external:
            return ExternalProofRouter(router, service.index.connection).route(
                ExternalProofDemand(
                    demand_ref=args.demand_ref,
                    external_obligation_ref=args.obligation_ref,
                    statement_digest=args.statement_digest,
                    query=args.query,
                    target_prover=args.target_prover,
                    claim_kind=args.claim_kind,
                    mathematical_status=args.mathematical_status,
                    statement_status=args.statement_status,
                    certification_status=args.certification_status,
                    da51_address=args.da51,
                    source_declaration=args.source_declaration,
                    current_source_hash=args.current_source_hash,
                ),
                limit=args.limit,
            )
        return router.route(
            ProofRouteRequest(
                query=args.query,
                target_prover=args.target_prover,
                claim_kind=args.claim_kind,
                mathematical_status=args.mathematical_status,
                statement_status=args.statement_status,
                certification_status=args.certification_status,
                da51_address=args.da51,
                source_declaration=args.source_declaration,
                current_source_hash=args.current_source_hash,
            ),
            limit=args.limit,
        )


def _prove(argv) -> int:
    parser = argparse.ArgumentParser(
        prog="dashi-repo prove",
        description="Discover-before-prove and route formalisation debt fail-closed.",
    )
    sub = parser.add_subparsers(dest="action", required=True)
    discover = sub.add_parser("discover")
    discover.add_argument("query")
    discover.add_argument("--limit", type=int, default=50)
    _common(discover)
    preflight = sub.add_parser("preflight")
    preflight.add_argument("target")
    preflight.add_argument("--errors-only", action="store_true")
    _common(preflight)
    route = sub.add_parser("route")
    _add_route_options(route)
    external = sub.add_parser("route-external-obligation")
    _add_route_options(external)
    external.add_argument("--demand-ref", required=True)
    external.add_argument("--obligation-ref", required=True)
    external.add_argument("--statement-digest", required=True)
    evidence = sub.add_parser("evidence-for-obligation")
    evidence.add_argument("--demand-ref", required=True)
    evidence.add_argument("--obligation-ref", required=True)
    evidence.add_argument("--statement-digest", required=True)
    _common(evidence)
    history = sub.add_parser("history")
    history.add_argument("--query")
    history.add_argument("--da51")
    history.add_argument("--limit", type=int, default=50)
    _common(history)
    args = parser.parse_args(argv)
    root = args.root.resolve()
    if args.action == "discover":
        return repository_main(["discover", args.query, "--limit", str(args.limit), "--root", str(root), "--database", str(args.database)])
    if args.action == "preflight":
        forwarded = ["diagnose", args.target, "--root", str(root), "--database", str(args.database)]
        if args.errors_only:
            forwarded.append("--errors-only")
        return repository_main(forwarded)
    if args.action == "history":
        with _connect(root, args.database) as conn:
            router = ProofRouter(discovery=lambda query, **kwargs: {}, connection=conn)
            for item in router.route_history(query=args.query, address=args.da51, limit=args.limit):
                print("route\t{}\t{}\t{}\t{}\t{}".format(item["route_id"], item["query"], item["debt_kind"], item["recommended_backend"], item["authority"]))
        return 0
    if args.action == "evidence-for-obligation":
        with _connect(root, args.database) as conn:
            base = ProofRouter(discovery=lambda query, **kwargs: {"query": query, "absence_claim_permitted": False, "absence_status": "not-requested"}, connection=conn)
            bridge = ExternalProofRouter(base, conn)
            rows = bridge.evidence_for_obligation(demand_ref=args.demand_ref, external_obligation_ref=args.obligation_ref, statement_digest=args.statement_digest)
            print(f"authority\tevidence-only")
            print(f"establishes_proof\tFalse")
            for item in rows:
                print("evidence\t{}\t{}\t{}\t{}\t{}\t{}".format(item["evidence_ref"], item["producer"], item["artifact_ref"], item["artifact_digest"], item["checker"], item["certification_state"]))
        return 0
    if args.action in {"route", "route-external-obligation"}:
        result = _service_route(args, root, external=args.action == "route-external-obligation")
        for key in (
            "route_id", "external_route_id", "demand_ref", "external_obligation_ref", "statement_digest",
            "debt_kind", "recommended_backend", "generation_permitted", "absence_status",
            "agda2lean_mapping_mode", "authority", "translation_establishes_proof", "establishes_proof",
        ):
            _print_scalar(key, result.get(key))
        if result.get("da51"):
            print(f"da51\t{result['da51']['address']}")
        for item in result.get("matches", ()):
            print(f"match\t{item['kind']}\t{item['symbol_id']}\t{item.get('similarity')}")
        return 0
    raise AssertionError(args.action)


def main(argv=None) -> int:
    actual = list(sys.argv[1:] if argv is None else argv)
    if actual and actual[0] == "status":
        return _status(actual[1:])
    if actual and actual[0] == "index":
        return _index(actual[1:])
    if actual and actual[0] == "harvest":
        return _harvest(actual[1:])
    if actual and actual[0] == "bootstrap":
        return _bootstrap(actual[1:])
    if actual and actual[0] == "da51":
        return _da51(actual[1:])
    if actual and actual[0] == "prove":
        return _prove(actual[1:])
    return repository_main(actual)


if __name__ == "__main__":
    raise SystemExit(main())
