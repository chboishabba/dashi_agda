#!/usr/bin/env python3
from __future__ import annotations

import argparse
import csv
import re
from collections import defaultdict, deque
from pathlib import Path
from typing import Dict, Iterable, List, Set, Tuple


ROOT_DIR = Path(__file__).resolve().parent.parent
IMPORT_RE = re.compile(r"^(?:open import|import)\s+([A-Za-z0-9_.]+)", re.MULTILINE)
DEFAULT_MONSTER = [
    "MonsterConformance",
    "MonsterGroups",
    "MonsterOntos",
    "MonsterSpec",
    "MonsterState",
    "MonsterTraceCounts",
    "MonsterVectors",
]
DEFAULT_CONTROL = [
    "Ultrametric",
    "Contraction",
    "CRTPeriod",
    "Base369",
    "FixedPoint",
]
SEMANTIC_FIELDS = ["eigenspace", "bott", "hecke", "da51", "orbifold", "j-fixed"]


def parse_csv_list(raw: str) -> List[str]:
    return [item.strip() for item in raw.split(",") if item.strip()]


def module_name_from_path(path: Path) -> str:
    rel = path.relative_to(ROOT_DIR).with_suffix("")
    return ".".join(rel.parts)


def collect_agda_files(paths: Iterable[str]) -> List[Path]:
    files: List[Path] = []
    for raw in paths:
        candidate = (ROOT_DIR / raw).resolve()
        if candidate.is_file() and candidate.suffix == ".agda":
            files.append(candidate)
            continue
        if candidate.is_dir():
            files.extend(
                sorted(
                    path
                    for path in candidate.rglob("*.agda")
                    if path.is_file() and not any(part.startswith(".") for part in path.parts)
                )
            )
    return sorted(set(files))


def parse_imports(text: str) -> List[str]:
    return IMPORT_RE.findall(text)


def bfs_reach(start: str, reverse_graph: Dict[str, Set[str]]) -> int:
    seen: Set[str] = set()
    todo: deque[str] = deque([start])
    while todo:
        current = todo.popleft()
        for nxt in reverse_graph.get(current, set()):
            if nxt in seen:
                continue
            seen.add(nxt)
            todo.append(nxt)
    return len(seen)


def shortest_distance_to_root(
    start: str,
    reverse_graph: Dict[str, Set[str]],
    root_names: Set[str],
) -> int:
    if start in root_names:
        return 0
    seen: Set[str] = {start}
    todo: deque[Tuple[str, int]] = deque([(start, 0)])
    while todo:
        current, depth = todo.popleft()
        for nxt in reverse_graph.get(current, set()):
            if nxt in root_names:
                return depth + 1
            if nxt in seen:
                continue
            seen.add(nxt)
            todo.append((nxt, depth + 1))
    return -1


def detect_field(text: str, patterns: Iterable[str], fallback: str = "<missing>") -> str:
    lowered = text.lower()
    for pattern in patterns:
        if pattern.lower() in lowered:
            return pattern
    return fallback


def load_seed_rows(path: Path) -> Dict[str, Dict[str, str]]:
    if not path.exists():
        return {}
    with path.open("r", encoding="utf-8", newline="") as fh:
        reader = csv.DictReader(fh)
        rows = list(reader)
    seed_rows: Dict[str, Dict[str, str]] = {}
    for row in rows:
        key = row.get("module", "").strip() or row.get("name", "").strip()
        if key:
            seed_rows[key] = row
    return seed_rows


def derive_eigenspace(reach: int, imports: int) -> str:
    if reach >= 100:
        return "Hub"
    if reach >= 8 or imports >= 6:
        return "Spoke"
    return "Earth"


def derive_bott(imports: int) -> str:
    if imports >= 6:
        return "C6"
    if imports >= 4:
        return "C5"
    return "C4"


def derive_hecke(detected: str, has_hecke_import: bool) -> str:
    if detected != "<missing>":
        return detected
    if has_hecke_import:
        return "Hecke"
    return "baseline"


def derive_da51(seed_eigenspace: str) -> str:
    mapping = {
        "Earth": "graph-earth",
        "Spoke": "graph-spoke",
        "Hub": "graph-hub",
    }
    return mapping.get(seed_eigenspace, "graph-unknown")


def derive_orbifold(detected: str) -> str:
    if detected != "<missing>":
        return detected
    return "baseline"


def derive_jfixed(detected: str) -> str:
    if detected != "<missing>":
        return "yes"
    return "no"


def choose_semantic_value(
    field: str,
    seed_row: Dict[str, str] | None,
    detected: str,
    heuristic: str,
) -> Tuple[str, str]:
    if seed_row:
        seeded = seed_row.get(field, "").strip()
        if seeded:
            return seeded, "seed"
    if detected != "<missing>":
        return detected, "text-detect"
    return heuristic, "graph-derived"


def main() -> int:
    parser = argparse.ArgumentParser(description="Build a best-effort JMD regime table from the local Agda tree")
    parser.add_argument(
        "--paths",
        default=".,Monster,DASHI,MDL,Ontology,Verification",
        help="comma-separated files/directories to scan",
    )
    parser.add_argument(
        "--monster-modules",
        default=",".join(DEFAULT_MONSTER),
        help="comma-separated module basenames to label as M",
    )
    parser.add_argument(
        "--control-modules",
        default=",".join(DEFAULT_CONTROL),
        help="comma-separated module basenames to label as O",
    )
    parser.add_argument(
        "--output",
        default=str(ROOT_DIR / "artifacts" / "regime_test" / "jmd_regime_table.csv"),
    )
    parser.add_argument(
        "--seed",
        default=str(ROOT_DIR / "data" / "regime_test" / "jmd_regime_seed.csv"),
        help="CSV file with curated semantic regime values keyed by module or name",
    )
    args = parser.parse_args()

    scan_paths = parse_csv_list(args.paths)
    monster_modules = set(parse_csv_list(args.monster_modules))
    control_modules = set(parse_csv_list(args.control_modules))
    seed_rows = load_seed_rows(Path(args.seed))
    files = collect_agda_files(scan_paths)
    if not files:
        raise SystemExit("no Agda files found")

    module_to_path: Dict[str, Path] = {}
    graph: Dict[str, Set[str]] = defaultdict(set)
    reverse_graph: Dict[str, Set[str]] = defaultdict(set)
    rows: List[Dict[str, str]] = []
    root_names = {"DASHI.Everything", *monster_modules, *control_modules}

    raw_records: List[Tuple[str, Path, str, List[str], List[str]]] = []
    for path in files:
        text = path.read_text(encoding="utf-8", errors="ignore")
        module_name = module_name_from_path(path)
        basename = path.stem
        imports = parse_imports(text)
        module_to_path[module_name] = path
        for imported in imports:
            graph[module_name].add(imported)
            reverse_graph[imported].add(module_name)
        raw_records.append((module_name, path, text, imports, [item.split(".")[-1] for item in imports]))

    for module_name, path, text, imports, import_basenames in raw_records:
        basename = path.stem
        if basename in monster_modules:
            group = "M"
        elif basename in control_modules:
            group = "O"
        else:
            group = "U"
        loc = text.count("\n") + 1
        import_count = len(imports)
        reach = bfs_reach(module_name, reverse_graph)
        depth = shortest_distance_to_root(module_name, reverse_graph, root_names)
        has_hecke_import = any("Hecke" in item for item in imports)
        has_monster_import = any("Monster" in item for item in imports)
        has_ultrametric_import = any("Ultrametric" in item for item in imports)
        has_contraction_import = any("Contraction" in item for item in imports)

        detected_hecke = detect_field(text, ["T_17", "T_47", "Hecke"])
        detected_eigenspace = detect_field(text, ["Earth", "Spoke", "Hub"])
        detected_da51 = detect_field(text, ["jB0E0", "jB0E1", "jB0E2", "jB0E3", "jB0E4", "jB0E5", "jB0E6", "jB0E7"])
        detected_orbifold = detect_field(text, ["orbifold", "mod 71", "mod 59", "mod 47"])
        detected_jfixed = "yes" if ("j-fixed" in text.lower() or "p47" in text) else "<missing>"
        detected_bott = detect_field(text, ["bott", "C4", "C5", "C6"])

        seed_row = seed_rows.get(module_name) or seed_rows.get(basename)
        heuristic_eigenspace = derive_eigenspace(reach, import_count)
        heuristic_bott = derive_bott(import_count)
        heuristic_hecke = derive_hecke(detected_hecke, has_hecke_import)
        heuristic_da51 = derive_da51(
            seed_row.get("eigenspace", "").strip() if seed_row and seed_row.get("eigenspace", "").strip() else heuristic_eigenspace
        )
        heuristic_orbifold = derive_orbifold(detected_orbifold)
        heuristic_jfixed = derive_jfixed(detected_jfixed)

        eigenspace, eigenspace_source = choose_semantic_value(
            "eigenspace", seed_row, detected_eigenspace, heuristic_eigenspace
        )
        bott, bott_source = choose_semantic_value(
            "bott", seed_row, detected_bott, heuristic_bott
        )
        hecke, hecke_source = choose_semantic_value(
            "hecke", seed_row, detected_hecke, heuristic_hecke
        )
        da51, da51_source = choose_semantic_value(
            "da51", seed_row, detected_da51, heuristic_da51
        )
        orbifold, orbifold_source = choose_semantic_value(
            "orbifold", seed_row, detected_orbifold, heuristic_orbifold
        )
        jfixed, jfixed_source = choose_semantic_value(
            "j-fixed", seed_row, detected_jfixed, heuristic_jfixed
        )
        rows.append(
            {
                "name": basename,
                "module": module_name,
                "group": group,
                "path": str(path.relative_to(ROOT_DIR)),
                "depth": str(depth),
                "reach": str(reach),
                "imports": str(import_count),
                "import_count": str(import_count),
                "loc": str(loc),
                "bytes": str(path.stat().st_size),
                "eigenspace": eigenspace,
                "eigenspace_source": eigenspace_source,
                "bott": bott,
                "bott_source": bott_source,
                "hecke": hecke,
                "hecke_source": hecke_source,
                "da51": da51,
                "da51_source": da51_source,
                "orbifold": orbifold,
                "orbifold_source": orbifold_source,
                "j-fixed": jfixed,
                "j-fixed_source": jfixed_source,
                "has_monster_import": "yes" if has_monster_import else "no",
                "has_hecke_import": "yes" if has_hecke_import else "no",
                "has_ultrametric_import": "yes" if has_ultrametric_import else "no",
                "has_contraction_import": "yes" if has_contraction_import else "no",
                "p47": "",
                "p59": "",
                "p71": "",
                "trivector_sum": "",
                "mass": "",
                "cycles": "",
                "instr": "",
                "ipc": "",
            }
        )

    output = Path(args.output)
    output.parent.mkdir(parents=True, exist_ok=True)
    fieldnames = list(rows[0].keys())
    with output.open("w", encoding="utf-8", newline="") as fh:
        writer = csv.DictWriter(fh, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(sorted(rows, key=lambda row: (row["group"], row["name"], row["module"])))

    print(f"wrote {len(rows)} rows to {output}")
    print(f"monster rows: {sum(1 for row in rows if row['group'] == 'M')}")
    print(f"control rows: {sum(1 for row in rows if row['group'] == 'O')}")
    print(f"unlabeled rows: {sum(1 for row in rows if row['group'] == 'U')}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
