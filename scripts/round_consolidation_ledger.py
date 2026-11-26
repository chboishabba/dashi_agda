#!/usr/bin/env python3
"""Build a fail-closed consolidation ledger for historical Agda Round files.

This is an audit/reporting tool. It never deletes or rewrites source files.
It answers the narrower question needed before deletion:

    historical Round module -> consumers -> evidence -> terminal recipient

Presence in a package manifest or a ``machineChecked`` status is not treated
as proof that a historical declaration has been consolidated.
"""

from __future__ import annotations

import argparse
import json
import re
from collections import defaultdict
from pathlib import Path
from typing import Any

try:
    from scripts.agda_import_cone import (
        DependencyIndex,
        ModuleRecord,
        parse_agda_file,
        reverse_cone,
    )
except ModuleNotFoundError:  # direct execution: python scripts/round_consolidation_ledger.py
    from agda_import_cone import DependencyIndex, ModuleRecord, parse_agda_file, reverse_cone


ROUND_MODULE_RE = re.compile(r"(?:^|\.)(?:R\d+|Round\d+)(?:[^.]|$)")
ROUND_FILE_RE = re.compile(r"(?:R\d+|Round\d+)")
DECL_RE = re.compile(r"^[ \t]*([A-Za-z][A-Za-z0-9_']*)[ \t]*:", re.MULTILINE)
# These are useful reachability aggregators, but are not declaration-level
# migration recipients by themselves.
UMBRELLA_MODULES = {
    "DASHI.Physics.YangMills.Everything",
    "DASHI.Physics.YangMills.YMClayAristotleGapParityEverything",
}


def _load_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def is_historical_round_module(module: str, path: Path) -> bool:
    return bool(ROUND_MODULE_RE.search(module) or ROUND_FILE_RE.search(path.name))


def _module_names(path: Path) -> set[str]:
    text = path.read_text(encoding="utf-8")
    return set(DECL_RE.findall(text))


def _manifest_recipients(manifest: dict[str, Any], repo_root: Path) -> list[str]:
    recipients: set[str] = set()
    for lemma in manifest.get("lemmas", []):
        for owner in lemma.get("source_owners", []):
            owner_path = repo_root / owner
            if owner_path.is_file():
                module = ".".join(owner_path.relative_to(repo_root).with_suffix("").parts)
                if not is_historical_round_module(module, owner_path):
                    recipients.add(module)
    return sorted(recipients)


def _split_declaration_id(value: str) -> tuple[str, str] | None:
    if value.count("::") != 1:
        return None
    module, name = value.split("::", 1)
    if not module or not name or "." not in module:
        return None
    return module, name


def validate_mapping(
    mapping: dict[str, str],
    index: Any,
    recipients: set[str] | None = None,
) -> list[str]:
    """Reject mappings that consolidate into another historical Round module."""

    errors: list[str] = []
    for source, target in sorted(mapping.items()):
        source_parts = _split_declaration_id(source)
        target_parts = _split_declaration_id(target)
        if source_parts is None:
            errors.append(f"{source}: source must be module::declaration")
            continue
        if target_parts is None:
            errors.append(f"{source}: target must be module::declaration")
            continue
        source_module, source_name = source_parts
        target_module, target_name = target_parts
        target_record = index.module_to_record.get(target_module)
        if target_record is None:
            errors.append(f"{source}: target module does not exist: {target_module}")
        elif is_historical_round_module(target_module, target_record.path):
            errors.append(f"{source}: target must be non-Round canonical module: {target}")
        elif recipients is not None and target_module not in recipients:
            errors.append(f"{source}: target module is not a manifest terminal recipient: {target_module}")
        elif target_name not in _module_names(target_record.path):
            errors.append(f"{source}: target declaration does not exist: {target}")
        if source_module not in index.module_to_record:
            errors.append(f"{source}: source module does not exist: {source_module}")
        else:
            source_record = index.module_to_record[source_module]
            if not is_historical_round_module(source_module, source_record.path):
                errors.append(f"{source}: source must be a historical Round module")
            elif source_name not in _module_names(source_record.path):
                errors.append(f"{source}: source declaration does not exist: {source}")
    return errors


def _package_indexes(source: Path) -> tuple[dict[str, list[dict[str, Any]]], dict[str, set[str]]]:
    """Index declarations by module and module body/signature evidence."""

    declarations: dict[str, list[dict[str, Any]]] = defaultdict(list)
    module_packages: dict[str, set[str]] = defaultdict(set)
    if not source.is_file():
        return declarations, module_packages
    with source.open(encoding="utf-8") as stream:
        for line in stream:
            if not line.strip():
                continue
            package = json.loads(line)
            package_id = str(package.get("package_id", ""))
            for module in package.get("round_modules", []):
                module_packages[module].add(package_id)
            for declaration in package.get("declarations", []):
                if isinstance(declaration, dict) and declaration.get("module"):
                    row = dict(declaration)
                    row["package_id"] = package_id
                    row["disposition"] = package.get("disposition")
                    row["unresolved_residuals"] = package.get("unresolved_residuals", [])
                    declarations[declaration["module"]].append(row)
    return declarations, module_packages


def _terminal_candidates(
    index: Any,
    module: str,
    recipients: set[str],
) -> list[str]:
    candidates = set(reverse_cone(index, module)).intersection(recipients)
    if module in recipients:
        candidates.add(module)
    return sorted(candidates)


def _declaration_evidence(
    module: str,
    declarations: dict[str, list[dict[str, Any]]],
    terminal_candidates: list[str],
) -> dict[str, Any]:
    historical = declarations.get(module, [])
    recipient_decls = [row for recipient in terminal_candidates for row in declarations.get(recipient, [])]
    recipient_exact = {
        (row.get("signature_sha256"), row.get("body_sha256"))
        for row in recipient_decls
        if row.get("signature_sha256") and row.get("body_sha256")
    }
    recipient_signatures = {row.get("signature_sha256") for row in recipient_decls if row.get("signature_sha256")}
    exact = []
    signature = []
    for row in historical:
        key = (row.get("signature_sha256"), row.get("body_sha256"))
        if key in recipient_exact:
            exact.append(row.get("name"))
        elif row.get("signature_sha256") in recipient_signatures:
            signature.append(row.get("name"))
    unresolved = sorted({residual for row in historical for residual in row.get("unresolved_residuals", [])})
    return {
        "historical_declaration_count": len(historical),
        "exact_recipient_matches": sorted(x for x in exact if x),
        "signature_recipient_matches": sorted(x for x in signature if x),
        "unresolved_residuals": unresolved,
    }


def _same_name_candidates(
    source_record: ModuleRecord,
    target_modules: list[str],
    index: Any,
) -> dict[str, list[str]]:
    """Find review-only same-name declaration candidates in canonical modules."""

    source_names = _module_names(source_record.path)
    candidates: dict[str, list[str]] = {}
    for target in target_modules:
        target_record = index.module_to_record.get(target)
        if target_record is None:
            continue
        common = sorted(source_names.intersection(_module_names(target_record.path)))
        if common:
            candidates[target] = common
    return candidates


def _verification_commands(
    record: ModuleRecord,
    mapping: dict[str, str],
    index: Any,
    repo_root: Path,
) -> list[str]:
    """Return only the repository-sanctioned Agda entrypoint commands."""

    modules = {record.module}
    for source, target in mapping.items():
        if source.split("::", 1)[0] == record.module:
            modules.add(target.split("::", 1)[0])
    commands: list[str] = []
    for module in sorted(modules):
        target_record = index.module_to_record.get(module)
        if target_record is None:
            continue
        relative = target_record.path.relative_to(repo_root).as_posix()
        commands.append(
            f"DASHI_NO_TMUX=1 scripts/run_agda29_parallel_check.sh {relative}"
        )
    return commands


def _build_scoped_index(repo_root: Path, scope: Path) -> DependencyIndex:
    paths = sorted(scope.rglob("*.agda"))
    files: list[ModuleRecord] = []
    module_to_record: dict[str, ModuleRecord] = {}
    path_to_module: dict[Path, str] = {}
    direct_imports: dict[str, tuple[str, ...]] = {}
    reverse: dict[str, set[str]] = defaultdict(set)
    for path in paths:
        if not path.is_file() or ".git" in path.parts:
            continue
        record = parse_agda_file(path, repo_root)
        files.append(record)
        module_to_record.setdefault(record.module, record)
        path_to_module[record.path] = record.module
        direct_imports[record.module] = record.imports
        for imported in record.imports:
            reverse[imported].add(record.module)
    return DependencyIndex(
        repo_root=repo_root,
        files=tuple(files),
        module_to_record=module_to_record,
        path_to_module=path_to_module,
        direct_imports=direct_imports,
        reverse_imports={key: tuple(sorted(value)) for key, value in reverse.items()},
    )


def build_ledger(
    repo_root: Path,
    package_source: Path,
    endpoint_manifest: Path,
    *,
    scope: Path | None = None,
    mapping: dict[str, str] | None = None,
    include_validation: bool = True,
) -> dict[str, Any]:
    index = _build_scoped_index(repo_root, scope or (repo_root / "DASHI/Physics/YangMills"))
    mapping = mapping or {}
    manifest = _load_json(endpoint_manifest)
    recipients = set(_manifest_recipients(manifest, repo_root))
    mapping_errors = validate_mapping(mapping, index, recipients)
    if mapping_errors:
        raise ValueError("invalid consolidation mapping:\n" + "\n".join(mapping_errors))
    declarations, module_packages = _package_indexes(package_source)
    rows: list[dict[str, Any]] = []

    for record in index.files:
        if not is_historical_round_module(record.module, record.path):
            continue
        if not include_validation and "Validation" in record.path.name:
            continue
        importers = sorted(index.reverse_imports.get(record.module, ()))
        nonhistorical_importers = [
            importer
            for importer in importers
            if not is_historical_round_module(
                importer,
                index.module_to_record[importer].path,
            )
        ]
        concrete_consumers = [
            importer for importer in nonhistorical_importers
            if importer not in UMBRELLA_MODULES
        ]
        reverse_consumers = sorted(
            consumer for consumer in reverse_cone(index, record.module)
            if consumer != record.module
        )
        reverse_nonhistorical_consumers = [
            consumer for consumer in reverse_consumers
            if not is_historical_round_module(
                consumer,
                index.module_to_record[consumer].path,
            )
        ]
        reverse_concrete_consumers = [
            consumer for consumer in reverse_nonhistorical_consumers
            if consumer not in UMBRELLA_MODULES
        ]
        reverse_umbrella_consumers = [
            consumer for consumer in reverse_nonhistorical_consumers
            if consumer in UMBRELLA_MODULES
        ]
        historical_only_consumers = [
            consumer for consumer in reverse_consumers
            if is_historical_round_module(
                consumer,
                index.module_to_record[consumer].path,
            )
        ]
        terminal_candidates = _terminal_candidates(index, record.module, recipients)
        preferred_targets = sorted(set(reverse_concrete_consumers).union(terminal_candidates))
        same_name_candidates = _same_name_candidates(record, preferred_targets, index)
        evidence = _declaration_evidence(record.module, declarations, terminal_candidates)
        package_ids = sorted(module_packages.get(record.module, set()))
        verification_commands = _verification_commands(record, mapping, index, repo_root)
        blockers: list[str] = []
        if nonhistorical_importers:
            blockers.append("current-nonhistorical-importers")
        if not terminal_candidates:
            blockers.append("no-terminal-recipient-consumer")
        if not evidence["exact_recipient_matches"] and not evidence["signature_recipient_matches"]:
            blockers.append("no-declaration-level-recipient-match")
        if evidence["unresolved_residuals"]:
            blockers.append("residual-package-evidence")
        if not package_ids:
            blockers.append("no-package-evidence")
        orphan_deletion_candidate = not importers and not any(
            source.split("::", 1)[0] == record.module for source in mapping
        )
        if orphan_deletion_candidate:
            migration_action = "delete-orphan-after-import-scan"
        elif reverse_concrete_consumers:
            migration_action = "rewire-nonhistorical-consumers"
        elif reverse_umbrella_consumers:
            migration_action = "rewire-umbrella-consumers"
        elif historical_only_consumers:
            migration_action = "delete-historical-island-after-import-scan"
        elif terminal_candidates:
            migration_action = "extract-into-canonical-recipient"
        else:
            migration_action = "assign-canonical-recipient"
        rows.append(
            {
                "module": record.module,
                "path": str(record.path.relative_to(repo_root)),
                "historical_kind": "validation" if "Validation" in record.path.name else "exact-or-source",
                "direct_imports": list(record.imports),
                "importer_count": len(importers),
                "importers": importers,
                "nonhistorical_importers": nonhistorical_importers,
                "canonical_consumer_modules": concrete_consumers,
                "reverse_cone_nonhistorical_consumers": reverse_nonhistorical_consumers,
                "reverse_cone_concrete_consumers": reverse_concrete_consumers,
                "reverse_cone_umbrella_consumers": reverse_umbrella_consumers,
                "historical_only_consumers": historical_only_consumers,
                "terminal_recipient_candidates": terminal_candidates,
                "preferred_canonical_targets": preferred_targets,
                "same_name_declaration_candidates": same_name_candidates,
                "orphan_deletion_candidate": orphan_deletion_candidate,
                "package_ids": package_ids,
                "declaration_evidence": evidence,
                "required_agda_verification_commands": verification_commands,
                "migration_action": migration_action,
                "deletion_blockers": blockers,
                "safe_to_delete": not blockers,
                "mapped_declarations": {
                    source: target
                    for source, target in mapping.items()
                    if source.split("::", 1)[0] == record.module
                },
            }
        )

    rows.sort(key=lambda row: row["module"])
    return {
        "schema_version": 1,
        "analyzer": "scripts/round_consolidation_ledger.py",
        "repo_root": str(repo_root),
        "package_source": str(package_source),
        "endpoint_manifest": str(endpoint_manifest),
        "terminal_recipient_count": len(recipients),
        "terminal_recipients": sorted(recipients),
        "historical_module_count": len(rows),
        "safe_to_delete_count": sum(row["safe_to_delete"] for row in rows),
        "blocked_module_count": sum(not row["safe_to_delete"] for row in rows),
        "deletion_policy": "fail closed: no deletion is authorized by this report; safe_to_delete requires a later reviewed rewiring and Agda check",
        "migration_goal": "remove every historical Round module after declaration extraction, import rewiring, and sanctioned Agda verification",
        "migration_action_counts": {
            "delete-orphan-after-import-scan": sum(
                row.get("migration_action") == "delete-orphan-after-import-scan" for row in rows
            ),
            "rewire-nonhistorical-consumers": sum(
                row.get("migration_action") == "rewire-nonhistorical-consumers" for row in rows
            ),
            "rewire-umbrella-consumers": sum(
                row.get("migration_action") == "rewire-umbrella-consumers" for row in rows
            ),
            "delete-historical-island-after-import-scan": sum(
                row.get("migration_action") == "delete-historical-island-after-import-scan" for row in rows
            ),
            "extract-into-canonical-recipient": sum(
                row.get("migration_action") == "extract-into-canonical-recipient" for row in rows
            ),
            "assign-canonical-recipient": sum(
                row.get("migration_action") == "assign-canonical-recipient" for row in rows
            ),
        },
        "mapping_policy": "mapping keys identify historical declarations as module::name; mapping targets identify non-Round canonical declarations as module::name",
        "mapping_count": len(mapping),
        "verification_policy": "run only scripts/run_agda29_parallel_check.sh after each reviewed rewiring",
        "modules": rows,
    }


def render_markdown(ledger: dict[str, Any]) -> str:
    lines = [
        "# Historical Round Consolidation Ledger",
        "",
        "Migration worklist: the goal is to remove every historical Round module after reviewed extraction and verification. This report does not yet rewrite or delete files.",
        "",
        f"- Historical modules: **{ledger['historical_module_count']}**",
        f"- Candidate terminal recipients: **{ledger['terminal_recipient_count']}**",
        f"- Currently safe to delete: **{ledger['safe_to_delete_count']}**",
        f"- Blocked: **{ledger['blocked_module_count']}**",
        f"- Delete unreferenced historical leaves after final import scan: **{ledger['migration_action_counts']['delete-orphan-after-import-scan']}**",
        f"- Rewire existing canonical consumers: **{ledger['migration_action_counts']['rewire-nonhistorical-consumers']}**",
        f"- Rewire umbrella consumers: **{ledger['migration_action_counts']['rewire-umbrella-consumers']}**",
        f"- Delete closed historical islands after import scan: **{ledger['migration_action_counts']['delete-historical-island-after-import-scan']}**",
        f"- Extract into an existing canonical recipient: **{ledger['migration_action_counts']['extract-into-canonical-recipient']}**",
        f"- Assign a canonical recipient first: **{ledger['migration_action_counts']['assign-canonical-recipient']}**",
        "",
        "A module is safe only after its consumers are rewired, its declarations are represented by a canonical recipient, and a reviewed Agda check passes.",
        "",
        "| Module | Kind | Migration action | Consumers | Terminal candidates | Evidence matches | Blockers |",
        "| --- | --- | --- | ---: | ---: | ---: | --- |",
    ]
    for row in ledger["modules"]:
        evidence = row["declaration_evidence"]
        matches = len(evidence["exact_recipient_matches"]) + len(evidence["signature_recipient_matches"])
        blockers = ", ".join(row["deletion_blockers"]) or "none"
        lines.append(
            f"| `{row['module']}` | {row['historical_kind']} | {row['migration_action']} | {row['importer_count']} | "
            f"{len(row['terminal_recipient_candidates'])} | {matches} | {blockers} |"
        )
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path("."))
    parser.add_argument("--scope", type=Path, default=Path("DASHI/Physics/YangMills"))
    parser.add_argument("--packages", type=Path, default=Path(".dashi/round-stranded/ym-packages.jsonl"))
    parser.add_argument("--endpoint-manifest", type=Path, default=Path("Docs/physics/YMClayEndpointPhaseLemmaManifest20261108.json"))
    parser.add_argument("--json-output", type=Path, default=Path(".dashi/round-stranded/ym-consolidation-ledger.json"))
    parser.add_argument("--markdown-output", type=Path, default=Path(".dashi/round-stranded/ym-consolidation-ledger.md"))
    parser.add_argument("--exclude-validation", action="store_true")
    parser.add_argument("--mapping", type=Path, help="JSON declaration mapping: {'historical.module::name': 'canonical.module::name'}")
    args = parser.parse_args()

    root = args.repo_root.resolve()
    mapping: dict[str, str] = {}
    if args.mapping:
        mapping_path = args.mapping if args.mapping.is_absolute() else root / args.mapping
        loaded = _load_json(mapping_path)
        mapping = loaded.get("declarations", loaded) if isinstance(loaded, dict) else {}
        if not all(isinstance(key, str) and isinstance(value, str) for key, value in mapping.items()):
            raise ValueError("mapping must contain string declaration keys and values")
    ledger = build_ledger(
        root,
        (root / args.packages).resolve() if not args.packages.is_absolute() else args.packages,
        (root / args.endpoint_manifest).resolve() if not args.endpoint_manifest.is_absolute() else args.endpoint_manifest,
        scope=(root / args.scope).resolve() if not args.scope.is_absolute() else args.scope,
        mapping=mapping,
        include_validation=not args.exclude_validation,
    )
    args.json_output.parent.mkdir(parents=True, exist_ok=True)
    args.json_output.write_text(json.dumps(ledger, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    args.markdown_output.parent.mkdir(parents=True, exist_ok=True)
    args.markdown_output.write_text(render_markdown(ledger), encoding="utf-8")
    print(json.dumps({key: ledger[key] for key in ("historical_module_count", "safe_to_delete_count", "blocked_module_count")}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
