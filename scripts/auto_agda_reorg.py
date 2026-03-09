#!/usr/bin/env python3

import argparse
import json
import pathlib
import re
import sys

ROOT = pathlib.Path(".").resolve()
DEFAULT_MANIFEST = pathlib.Path("scripts/reorg_manifest.json")

MODULE_HEADER_RE = re.compile(r"^(\s*module\s+)([A-Za-z0-9_./]+)(\s+where\b)", re.MULTILINE)
IMPORT_OPEN_RE = re.compile(r"^(\s*open\s+import\s+)([A-Za-z0-9_./]+)\b", re.MULTILINE)
IMPORT_RE = re.compile(r"^(\s*import\s+)([A-Za-z0-9_./]+)\b", re.MULTILINE)
OPEN_RE = re.compile(r"^(\s*open\s+)([A-Za-z0-9_./]+)\b", re.MULTILINE)
ALIAS_RE = re.compile(r"^(\s*module\s+\w+\s*=\s*)([A-Za-z0-9_./]+)\b", re.MULTILINE)


def fail(message):
    print(f"ERROR: {message}", file=sys.stderr)
    sys.exit(1)


def norm_path(path):
    return pathlib.Path(path).resolve()


def rel_path(path):
    return path.relative_to(ROOT)


def find_agda_files():
    return sorted(p for p in ROOT.rglob("*.agda") if p.is_file())


def module_from_path(path):
    rel = rel_path(path).with_suffix("")
    return ".".join(rel.parts)


def path_from_module(module):
    return ROOT / (module.replace(".", "/") + ".agda")


def canonical_module_token(token):
    return token.replace("/", ".")


def parse_manifest(path):
    if not path.exists():
        fail(f"Manifest not found: {path}")

    suffix = path.suffix.lower()
    raw = None
    if suffix == ".json":
        raw = json.loads(path.read_text())
    elif suffix in {".yaml", ".yml"}:
        try:
            import yaml  # type: ignore
        except ImportError:
            fail("YAML manifest requested but PyYAML is not installed; use JSON manifest.")
        raw = yaml.safe_load(path.read_text())
    else:
        fail(f"Unsupported manifest extension: {path.suffix}")

    prefix_entries = []
    if isinstance(raw, dict):
        entries = raw.get("renames", [])
        prefix_entries = raw.get("prefix_renames", [])
    else:
        entries = raw

    if not isinstance(entries, list):
        fail("Manifest must be a list of rename entries or {\"renames\": [...]}.")
    if not isinstance(prefix_entries, list):
        fail("Manifest key 'prefix_renames' must be a list when present.")

    parsed = []
    for idx, entry in enumerate(entries):
        if not isinstance(entry, dict):
            fail(f"Manifest entry {idx} is not an object.")
        if "from" not in entry or "to" not in entry:
            fail(f"Manifest entry {idx} must have 'from' and 'to'.")
        parsed.append((str(entry["from"]).strip(), str(entry["to"]).strip()))

    parsed_prefixes = []
    for idx, entry in enumerate(prefix_entries):
        if not isinstance(entry, dict):
            fail(f"Manifest prefix entry {idx} is not an object.")
        if "from_prefix" not in entry or "to_prefix" not in entry:
            fail(
                f"Manifest prefix entry {idx} must have 'from_prefix' and 'to_prefix'."
            )
        exact_to = entry.get("exact_to")
        if exact_to is not None:
            exact_to = str(exact_to).strip()
        parsed_prefixes.append(
            {
                "from_prefix": str(entry["from_prefix"]).strip(),
                "to_prefix": str(entry["to_prefix"]).strip(),
                "exact_to": exact_to,
            }
        )
    return parsed, parsed_prefixes


def module_or_path_to_module_and_path(value):
    value = value.strip()

    if value.endswith(".agda"):
        rel = pathlib.Path(value)
        if rel.is_absolute():
            fail(f"Manifest path must be repo-relative: {value}")
        path = ROOT / rel
        module = ".".join(rel.with_suffix("").parts)
        return module, path

    if "/" in value:
        rel = pathlib.Path(value + ("" if value.endswith(".agda") else ".agda"))
        path = ROOT / rel
        module = ".".join(rel.with_suffix("").parts)
        return module, path

    # Treat everything else as a dotted module.
    module = value
    return module, path_from_module(module)


def normalize_manifest(entries):
    normalized = []
    seen_from = set()
    seen_to = set()

    for from_raw, to_raw in entries:
        old_mod, old_path = module_or_path_to_module_and_path(from_raw)
        new_mod, new_path = module_or_path_to_module_and_path(to_raw)

        old_mod = canonical_module_token(old_mod)
        new_mod = canonical_module_token(new_mod)

        if old_mod == new_mod:
            fail(f"No-op rename is not allowed: {old_mod}")

        if old_mod in seen_from:
            fail(f"Duplicate 'from' module in manifest: {old_mod}")
        if new_mod in seen_to:
            fail(f"Duplicate 'to' module in manifest: {new_mod}")

        seen_from.add(old_mod)
        seen_to.add(new_mod)
        normalized.append(
            {
                "old_module": old_mod,
                "new_module": new_mod,
                "old_path": norm_path(old_path),
                "new_path": norm_path(new_path),
            }
        )

    return normalized


def normalize_prefix_rules(prefix_entries):
    normalized = []
    seen_from = set()

    for entry in prefix_entries:
        from_prefix = canonical_module_token(entry["from_prefix"])
        to_prefix = canonical_module_token(entry["to_prefix"])
        exact_to = entry["exact_to"]
        if exact_to is not None:
            exact_to = canonical_module_token(exact_to)

        if not from_prefix or not to_prefix:
            fail("Prefix renames must not be empty.")
        if from_prefix == to_prefix and exact_to is None:
            fail(f"No-op prefix rename is not allowed: {from_prefix}")
        if from_prefix in seen_from:
            fail(f"Duplicate 'from_prefix' in manifest: {from_prefix}")
        if exact_to == from_prefix:
            fail(f"No-op exact_to in prefix rename is not allowed: {from_prefix}")

        seen_from.add(from_prefix)
        normalized.append(
            {
                "from_prefix": from_prefix,
                "to_prefix": to_prefix,
                "exact_to": exact_to,
            }
        )

    return normalized


def prefix_match(module_name, prefix):
    return module_name == prefix or module_name.startswith(prefix)


def expand_prefix_rules(prefix_rules, explicit_entries):
    explicit_old = {entry["old_module"] for entry in explicit_entries}
    explicit_new = {entry["new_module"] for entry in explicit_entries}
    modules = {module_from_path(path) for path in find_agda_files()}
    expanded = []

    for rule in prefix_rules:
        from_prefix = rule["from_prefix"]
        to_prefix = rule["to_prefix"]
        exact_to = rule["exact_to"]
        matched = sorted(
            module_name
            for module_name in modules
            if prefix_match(module_name, from_prefix)
        )

        if not matched:
            already_moved = sorted(
                module_name
                for module_name in modules
                if (
                    module_name == to_prefix.rstrip(".")
                    or module_name.startswith(to_prefix)
                    or (exact_to is not None and module_name == exact_to)
                )
            )
            if already_moved:
                continue
            fail(f"Prefix rule matched no modules: {from_prefix}")

        for old_module in matched:
            if old_module in explicit_old:
                continue

            if old_module == from_prefix:
                if exact_to is None:
                    fail(
                        f"Prefix rule {from_prefix} matched an exact module but no exact_to was provided"
                    )
                new_module = exact_to
            else:
                suffix = old_module[len(from_prefix):]
                new_module = to_prefix + suffix

            if new_module in explicit_new:
                fail(
                    f"Prefix rule for {from_prefix} collides with explicit target {new_module}"
                )

            expanded.append(
                {
                    "old_module": old_module,
                    "new_module": new_module,
                    "old_path": norm_path(path_from_module(old_module)),
                    "new_path": norm_path(path_from_module(new_module)),
                }
            )

    return expanded


def split_camel(name):
    return re.findall(r"[A-Z][a-z0-9]*|[A-Z0-9]+(?=[A-Z][a-z]|$)", name)


def suggest_prefix_rules():
    modules = sorted(module_from_path(path) for path in find_agda_files())
    suggestions = []
    seen = set()
    family_markers = [
        "Regime",
        "Validation",
        "Summary",
        "Report",
        "Instance",
        "Shift",
        "Witness",
        "Proof",
    ]

    for module_name in modules:
        stem = module_name.split(".")[-1]
        parts = split_camel(stem)
        if len(parts) < 4:
            continue

        for marker in family_markers:
            if marker not in parts[:-1]:
                continue
            idx = parts.index(marker)
            if idx < 2:
                continue

            from_prefix_stem = "".join(parts[: idx + 1])
            suffix_parts = parts[idx + 1 :]
            if not suffix_parts:
                continue

            prefix = ".".join(module_name.split(".")[:-1] + [from_prefix_stem])
            members = [
                candidate
                for candidate in modules
                if candidate == prefix or candidate.startswith(prefix)
            ]
            if len(members) < 4:
                continue

            target_prefix = ".".join(module_name.split(".")[:-1] + ["".join(parts[:idx]), marker, ""])
            key = (prefix, target_prefix)
            if key in seen:
                continue
            seen.add(key)
            suggestions.append((len(members), prefix, target_prefix))

    for count, from_prefix, to_prefix in sorted(suggestions, reverse=True):
        print(
            json.dumps(
                {
                    "count": count,
                    "from_prefix": from_prefix,
                    "to_prefix": to_prefix,
                }
            )
        )


def derive_corruption_repairs(rename_map):
    repairs = {}
    pairs = sorted(rename_map.items(), key=lambda kv: len(kv[0]))
    for old_a, new_a in pairs:
        for old_b, new_b in pairs:
            if old_a == old_b:
                continue
            if old_b.startswith(old_a):
                bad = new_a + old_b[len(old_a) :]
                if bad != new_b:
                    repairs[bad] = new_b
    return repairs


def build_state(normalized_entries):
    rename_map = {entry["old_module"]: entry["new_module"] for entry in normalized_entries}
    repair_map = derive_corruption_repairs(rename_map)

    moves = []
    move_targets = {}

    for entry in normalized_entries:
        old_path = entry["old_path"]
        new_path = entry["new_path"]
        old_exists = old_path.is_file()
        new_exists = new_path.is_file()

        if old_exists and not new_exists:
            if new_path in move_targets:
                fail(
                    "Two manifest entries target the same file: "
                    f"{rel_path(new_path)}"
                )
            move_targets[new_path] = entry["old_module"]
            moves.append(entry)
        elif old_exists and new_exists:
            fail(
                f"Both source and target exist for {entry['old_module']}: "
                f"{rel_path(old_path)} and {rel_path(new_path)}"
            )
        elif (not old_exists) and new_exists:
            # Already moved; keep mapping for rewrite/check.
            continue
        else:
            fail(
                f"Neither source nor target exists for {entry['old_module']}: "
                f"{rel_path(old_path)} and {rel_path(new_path)}"
            )

    for move in moves:
        parent = move["new_path"].parent
        if parent.exists() and not parent.is_dir():
            fail(f"Target parent is not a directory: {rel_path(parent)}")

    # Future module set after moves.
    module_set = set(module_from_path(p) for p in find_agda_files())
    for entry in normalized_entries:
        old = entry["old_module"]
        new = entry["new_module"]
        if old in module_set:
            module_set.remove(old)
        module_set.add(new)

    return moves, rename_map, repair_map, module_set


def merge_entries(explicit_entries, prefix_entries):
    merged = []
    seen_from = set()
    seen_to = set()

    for entry in explicit_entries + prefix_entries:
        old_mod = entry["old_module"]
        new_mod = entry["new_module"]

        if old_mod == new_mod:
            continue
        if old_mod in seen_from:
            fail(f"Duplicate source module after manifest expansion: {old_mod}")
        if new_mod in seen_to:
            fail(f"Duplicate target module after manifest expansion: {new_mod}")

        seen_from.add(old_mod)
        seen_to.add(new_mod)
        merged.append(entry)

    return merged


def rewrite_token(token, rename_map, repair_map):
    canonical = canonical_module_token(token)
    canonical = repair_map.get(canonical, canonical)
    canonical = rename_map.get(canonical, canonical)
    return canonical


def rewrite_matches(text, regex, rename_map, repair_map, stats):
    def repl(match):
        prefix = match.group(1)
        token = match.group(2)
        rewritten = rewrite_token(token, rename_map, repair_map)
        if rewritten != token:
            stats["refs_rewritten"] += 1
        return f"{prefix}{rewritten}"

    return regex.sub(repl, text)


def rewrite_file_text(text, rename_map, repair_map):
    stats = {"refs_rewritten": 0}
    new_text = text

    # Module header first; it is a single declaration and must be canonical dotted form.
    def rewrite_module_header(match):
        prefix = match.group(1)
        token = match.group(2)
        suffix = match.group(3)
        rewritten = rewrite_token(token, rename_map, repair_map)
        if rewritten != token:
            stats["refs_rewritten"] += 1
        return f"{prefix}{rewritten}{suffix}"

    new_text = MODULE_HEADER_RE.sub(rewrite_module_header, new_text)
    new_text = rewrite_matches(new_text, IMPORT_OPEN_RE, rename_map, repair_map, stats)
    new_text = rewrite_matches(new_text, IMPORT_RE, rename_map, repair_map, stats)
    new_text = rewrite_matches(new_text, ALIAS_RE, rename_map, repair_map, stats)
    new_text = rewrite_matches(new_text, OPEN_RE, rename_map, repair_map, stats)
    return new_text, stats


def apply_moves(moves):
    moved = 0
    headers_rewritten = 0

    for move in moves:
        old_file = move["old_path"]
        new_file = move["new_path"]
        old_module = move["old_module"]
        new_module = move["new_module"]

        print(f"MOVE {rel_path(old_file)} -> {rel_path(new_file)}")
        text = old_file.read_text()
        rewritten, stats = rewrite_file_text(text, {old_module: new_module}, {})

        new_file.parent.mkdir(parents=True, exist_ok=True)
        new_file.write_text(rewritten)
        old_file.unlink()

        moved += 1
        if stats["refs_rewritten"] > 0:
            headers_rewritten += 1

    return moved, headers_rewritten


def rewrite_all_files(rename_map, repair_map, write):
    files_rewritten = 0
    refs_rewritten = 0

    for path in find_agda_files():
        old = path.read_text()
        new, stats = rewrite_file_text(old, rename_map, repair_map)
        if new != old:
            print(f"REWRITE {rel_path(path)}")
            files_rewritten += 1
            refs_rewritten += stats["refs_rewritten"]
            if write:
                path.write_text(new)

    return files_rewritten, refs_rewritten


def check_repo(rename_map):
    slash_module = []
    slash_imports = []
    stale_refs = []

    old_modules = sorted(rename_map.keys(), key=len, reverse=True)

    for path in find_agda_files():
        text = path.read_text()

        for m in MODULE_HEADER_RE.finditer(text):
            token = m.group(2)
            if "/" in token:
                slash_module.append((path, token))

        for regex in (IMPORT_OPEN_RE, IMPORT_RE, OPEN_RE, ALIAS_RE):
            for m in regex.finditer(text):
                token = m.group(2)
                if "/" in token:
                    slash_imports.append((path, token))

        for old in old_modules:
            pattern = re.compile(
                rf"(^\s*module\s+{re.escape(old)}(?![A-Za-z0-9_./])\s+where\b)|"
                rf"(^\s*open\s+import\s+{re.escape(old)}(?![A-Za-z0-9_./]))|"
                rf"(^\s*import\s+{re.escape(old)}(?![A-Za-z0-9_./]))|"
                rf"(^\s*open\s+{re.escape(old)}(?![A-Za-z0-9_./]))|"
                rf"(^\s*module\s+\w+\s*=\s*{re.escape(old)}(?![A-Za-z0-9_./]))",
                re.MULTILINE,
            )
            if pattern.search(text):
                stale_refs.append((path, old))

    if slash_module:
        fail(
            "Slash-style module declarations remain, e.g. "
            f"{rel_path(slash_module[0][0])}: {slash_module[0][1]}"
        )
    if slash_imports:
        fail(
            "Slash-style imports/opens remain, e.g. "
            f"{rel_path(slash_imports[0][0])}: {slash_imports[0][1]}"
        )
    if stale_refs:
        fail(
            "Old module references remain, e.g. "
            f"{rel_path(stale_refs[0][0])}: {stale_refs[0][1]}"
        )


def print_plan(moves, rename_map, repair_map):
    print("Reorganisation plan")
    print()
    if not moves:
        print("(No file moves needed)")
    else:
        for move in sorted(moves, key=lambda x: x["old_module"]):
            print(f"{move['old_module']} -> {move['new_module']}")
            print(f"  {rel_path(move['old_path'])}")
            print(f"  -> {rel_path(move['new_path'])}")
            print()

    print("Rename mappings:")
    for old, new in sorted(rename_map.items()):
        print(f"  {old} -> {new}")
    print()

    if repair_map:
        print("Corruption repairs:")
        for old, new in sorted(repair_map.items()):
            print(f"  {old} -> {new}")
        print()


def main():
    parser = argparse.ArgumentParser(description="Safe Agda module reorganizer")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--dry-run", action="store_true", help="show plan only (default)")
    mode.add_argument("--apply", action="store_true", help="apply moves and rewrites")
    mode.add_argument("--check", action="store_true", help="check for drift and stale refs")
    mode.add_argument(
        "--suggest-prefixes",
        action="store_true",
        help="print candidate prefix_renames inferred from repeated module families",
    )
    parser.add_argument(
        "--manifest",
        type=pathlib.Path,
        default=DEFAULT_MANIFEST,
        help=f"manifest path (default: {DEFAULT_MANIFEST})",
    )
    parser.add_argument("--repo-root", type=pathlib.Path, default=pathlib.Path("."))
    args = parser.parse_args()

    global ROOT
    ROOT = args.repo_root.resolve()

    if args.suggest_prefixes:
        suggest_prefix_rules()
        return

    entries, prefix_entries = parse_manifest(args.manifest)
    normalized = normalize_manifest(entries)
    normalized_prefixes = normalize_prefix_rules(prefix_entries)
    expanded_prefix_entries = expand_prefix_rules(normalized_prefixes, normalized)
    merged_entries = merge_entries(normalized, expanded_prefix_entries)
    moves, rename_map, repair_map, _module_set = build_state(merged_entries)

    if args.check:
        check_repo(rename_map)
        print("CHECK OK")
        return

    print_plan(moves, rename_map, repair_map)
    files_rewritten, refs_rewritten = rewrite_all_files(
        rename_map, repair_map, write=False
    )
    print(
        f"Dry rewrite impact: files={files_rewritten}, refs={refs_rewritten}"
    )

    if args.apply:
        moved, headers = apply_moves(moves)
        files_rewritten, refs_rewritten = rewrite_all_files(
            rename_map, repair_map, write=True
        )
        check_repo(rename_map)
        print(
            "DONE "
            f"(moved={moved}, move_headers={headers}, "
            f"rewritten_files={files_rewritten}, rewritten_refs={refs_rewritten})"
        )


if __name__ == "__main__":
    main()
