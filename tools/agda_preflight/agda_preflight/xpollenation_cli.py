from __future__ import annotations

import argparse
import json
from pathlib import Path
import sqlite3
import sys

from .repository_store import DEFAULT_REPOSITORY_DB
from .xpollenation import XPollenationStore


def _common(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--database", type=Path, default=DEFAULT_REPOSITORY_DB)


def _connect(root: Path, database: Path) -> sqlite3.Connection:
    path = database if database.is_absolute() else root / database
    path.parent.mkdir(parents=True, exist_ok=True)
    conn = sqlite3.connect(path)
    conn.row_factory = sqlite3.Row
    conn.execute("PRAGMA journal_mode=WAL")
    conn.execute("PRAGMA synchronous=NORMAL")
    conn.execute("PRAGMA foreign_keys=ON")
    conn.execute("PRAGMA busy_timeout=5000")
    return conn


def _load(path: Path) -> dict:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"{path} must contain one JSON object")
    return value


def _print_neighbourhood(item: dict) -> None:
    subject = item["subject"]
    print(f"subject\t{subject['namespace']}:{subject['identifier']}")
    print(f"da51\t{item.get('da51_address')}")
    print(f"authority\t{item['authority']}")
    print(f"establishes_proof\t{item['establishes_proof']}")
    print(f"establishes_payment\t{item['establishes_payment']}")
    artifact = item.get("artifact")
    if artifact:
        print(
            "artifact\t{}\t{}\t{}".format(
                artifact["logical_artifact_ref"],
                artifact["content_digest"],
                artifact.get("cid"),
            )
        )
    for edge in item.get("edges", ()):
        print(
            "edge\t{}\t{}:{}\t{}\t{}:{}\t{}".format(
                edge["edge_id"],
                edge["subject_namespace"],
                edge["subject_identifier"],
                edge["relation_kind"],
                edge["object_namespace"],
                edge["object_identifier"],
                edge["status"],
            )
        )


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(
        prog="dashi-repo-xpollenation",
        description="Persist/query authority-neutral cross-domain xPollenation neighbourhoods in the shared repository-intelligence DB.",
    )
    sub = parser.add_subparsers(dest="action", required=True)

    ingest = sub.add_parser("ingest")
    ingest.add_argument("--input", type=Path, required=True)
    ingest.add_argument("--da51")
    ingest.add_argument("--artifact-resolution-receipt", type=Path)
    _common(ingest)

    show = sub.add_parser("show")
    show.add_argument("namespace")
    show.add_argument("identifier")
    _common(show)

    by_da51 = sub.add_parser("for-da51")
    by_da51.add_argument("address")
    _common(by_da51)

    args = parser.parse_args(sys.argv[1:] if argv is None else argv)
    root = args.root.resolve()
    with _connect(root, args.database) as conn:
        store = XPollenationStore(conn)
        if args.action == "ingest":
            receipt = (
                _load(args.artifact_resolution_receipt)
                if args.artifact_resolution_receipt is not None
                else None
            )
            result = store.ingest_neighbourhood(
                _load(args.input),
                da51_address=args.da51,
                artifact_resolution_receipt=receipt,
            )
            print(f"subject\t{result['subject']['namespace']}:{result['subject']['identifier']}")
            print(f"edge_count\t{result['edge_count']}")
            print(f"da51\t{result['da51_address']}")
            print(f"authority\t{result['authority']}")
            print(f"establishes_proof\t{result['establishes_proof']}")
            print(f"establishes_payment\t{result['establishes_payment']}")
            if result["artifact"]:
                print(f"artifact\t{result['artifact']['logical_artifact_ref']}")
            return 0
        if args.action == "show":
            item = store.neighbourhood(args.namespace, args.identifier)
            if item is None:
                return 1
            _print_neighbourhood(item)
            return 0
        if args.action == "for-da51":
            rows = store.neighbourhoods_for_da51(args.address)
            print(f"count\t{len(rows)}")
            for item in rows:
                _print_neighbourhood(item)
            return 0
    raise AssertionError(args.action)


if __name__ == "__main__":
    raise SystemExit(main())
