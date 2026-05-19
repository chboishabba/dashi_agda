#!/usr/bin/env python3
from __future__ import annotations

import argparse
import csv
import json
import math
import random
import re
from collections import Counter, defaultdict
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

ROOT_DIR = Path(__file__).resolve().parent.parent
ARROW_PROFILES: Dict[str, float] = {
    "strict": 0.0,
    "boundary": 1e-2,
    "lenient": 1e-1,
}
EIGEN_LABELS = ("Earth", "Spoke", "Hub")


DEFAULT_CATEGORICAL = ["eigenspace", "bott", "hecke", "da51"]
DEFAULT_JOINT = ["eigenspace", "bott", "hecke"]
DEFAULT_NUMERIC = [
    "p47",
    "p59",
    "p71",
    "trivector_sum",
    "cos",
    "l2",
    "depth",
    "reach",
    "imports",
    "mass",
    "cycles",
    "instr",
    "ipc",
    "orb71",
    "orb59",
    "orb47",
]


def parse_csv_list(raw: str | None, fallback: Sequence[str]) -> List[str]:
    if raw is None:
        return list(fallback)
    values = [item.strip() for item in raw.split(",")]
    return [item for item in values if item]


def load_rows(path: Path) -> List[Dict[str, str]]:
    with path.open("r", encoding="utf-8", newline="") as fh:
        reader = csv.DictReader(fh)
        rows = list(reader)
    if not rows:
        raise SystemExit(f"no rows found in {path}")
    return rows


def inject_default_group(
    rows: Sequence[Dict[str, str]],
    group_column: str,
    default_group: str | None,
) -> List[Dict[str, str]]:
    if group_column in rows[0]:
        return [dict(row) for row in rows]
    if default_group is None:
        return [dict(row) for row in rows]
    injected: List[Dict[str, str]] = []
    for row in rows:
        item = dict(row)
        item[group_column] = default_group
        injected.append(item)
    return injected


def require_columns(rows: Sequence[Dict[str, str]], columns: Iterable[str]) -> None:
    header = set(rows[0].keys())
    missing = [column for column in columns if column not in header]
    if missing:
        raise SystemExit(f"missing required columns: {', '.join(missing)}")


def split_groups(
    rows: Sequence[Dict[str, str]],
    group_column: str,
    monster_label: str,
    control_label: str,
) -> Tuple[List[Dict[str, str]], List[Dict[str, str]]]:
    monster = [row for row in rows if row.get(group_column) == monster_label]
    control = [row for row in rows if row.get(group_column) == control_label]
    if not monster or not control:
        raise SystemExit(
            f"expected rows for both groups in column '{group_column}' "
            f"with labels '{monster_label}' and '{control_label}'"
        )
    return monster, control


def count_values(rows: Sequence[Dict[str, str]], feature: str) -> Counter[str]:
    counts: Counter[str] = Counter()
    for row in rows:
        value = row.get(feature, "").strip()
        if value:
            counts[value] += 1
    return counts


def count_joint(rows: Sequence[Dict[str, str]], features: Sequence[str]) -> Counter[str]:
    counts: Counter[str] = Counter()
    for row in rows:
        values = [row.get(feature, "").strip() or "<missing>" for feature in features]
        counts[" | ".join(values)] += 1
    return counts


def count_transitions(
    rows: Sequence[Dict[str, str]], from_column: str, to_column: str
) -> Counter[str]:
    counts: Counter[str] = Counter()
    for row in rows:
        left = row.get(from_column, "").strip() or "<missing>"
        right = row.get(to_column, "").strip() or "<missing>"
        counts[f"{left} -> {right}"] += 1
    return counts


def aligned_probabilities(
    left: Counter[str], right: Counter[str]
) -> Tuple[List[str], List[float], List[float]]:
    keys = sorted(set(left) | set(right))
    left_total = sum(left.values())
    right_total = sum(right.values())
    left_probs = [left.get(key, 0) / left_total if left_total else 0.0 for key in keys]
    right_probs = [right.get(key, 0) / right_total if right_total else 0.0 for key in keys]
    return keys, left_probs, right_probs


def kl_divergence(p: Sequence[float], q: Sequence[float]) -> float:
    total = 0.0
    for p_i, q_i in zip(p, q):
        if p_i == 0.0:
            continue
        total += p_i * math.log2(p_i / q_i)
    return total


def jensen_shannon(p: Sequence[float], q: Sequence[float]) -> float:
    m = [(p_i + q_i) / 2.0 for p_i, q_i in zip(p, q)]
    return math.sqrt((kl_divergence(p, m) + kl_divergence(q, m)) / 2.0)


def permutation_p_value(
    rows: Sequence[Dict[str, str]],
    labels: Sequence[str],
    feature_counts: callable,
    group_column: str,
    monster_label: str,
    control_label: str,
    iterations: int,
    seed: int,
) -> float:
    rng = random.Random(seed)
    working = [dict(row) for row in rows]
    observed_monster = [row for row in working if row[group_column] == monster_label]
    observed_control = [row for row in working if row[group_column] == control_label]
    observed_keys, observed_pm, observed_po = aligned_probabilities(
        feature_counts(observed_monster), feature_counts(observed_control)
    )
    observed = jensen_shannon(observed_pm, observed_po)
    exceed = 0
    shuffled_labels = list(labels)
    for _ in range(iterations):
        rng.shuffle(shuffled_labels)
        for row, label in zip(working, shuffled_labels):
            row[group_column] = label
        perm_monster = [row for row in working if row[group_column] == monster_label]
        perm_control = [row for row in working if row[group_column] == control_label]
        _, pm, po = aligned_probabilities(feature_counts(perm_monster), feature_counts(perm_control))
        stat = jensen_shannon(pm, po)
        if stat >= observed:
            exceed += 1
    return (exceed + 1) / (iterations + 1)


def safe_float(raw: str) -> float | None:
    text = raw.strip()
    if not text:
        return None
    try:
        return float(text)
    except ValueError:
        return None


def numeric_summary(rows: Sequence[Dict[str, str]], feature: str) -> Dict[str, float] | None:
    values = [value for value in (safe_float(row.get(feature, "")) for row in rows) if value is not None]
    if not values:
        return None
    mean = sum(values) / len(values)
    variance = sum((value - mean) ** 2 for value in values) / len(values)
    return {
        "count": float(len(values)),
        "mean": mean,
        "min": min(values),
        "max": max(values),
        "stddev": math.sqrt(variance),
    }


def format_counts(counter: Counter[str], top_n: int) -> str:
    if not counter:
        return "(none)"
    parts = [f"{key}={value}" for key, value in counter.most_common(top_n)]
    return ", ".join(parts)


def build_step_embedding(
    row: Dict[str, str],
    columns: Sequence[str],
    log_columns: set[str],
) -> List[float]:
    values: List[float] = []
    for column in columns:
        raw = row.get(column, "")
        value = safe_float(raw)
        if value is None:
            raise SystemExit(f"step row missing numeric value for embedding column '{column}'")
        if column in log_columns:
            values.append(math.log1p(value))
        else:
            values.append(value)
    return values


def vector_subtract(left: Sequence[float], right: Sequence[float]) -> List[float]:
    return [l_i - r_i for l_i, r_i in zip(left, right)]


def vector_norm(values: Sequence[float]) -> float:
    return math.sqrt(sum(value * value for value in values))


def mean(values: Sequence[float]) -> float:
    return sum(values) / len(values) if values else 0.0


def energy_from_embedding(
    embedding: Sequence[float],
    columns: Sequence[str],
    weights: Dict[str, float],
) -> float:
    total = 0.0
    for value, column in zip(embedding, columns):
        total += weights.get(column, 0.0) * value
    return total


def group_step_rows(
    rows: Sequence[Dict[str, str]], name_column: str, time_column: str
) -> Dict[str, List[Dict[str, str]]]:
    grouped: Dict[str, List[Dict[str, str]]] = {}
    for row in rows:
        name = row.get(name_column, "").strip()
        if not name:
            raise SystemExit(f"step row missing name column '{name_column}'")
        grouped.setdefault(name, []).append(row)
    for name, items in grouped.items():
        try:
            items.sort(key=lambda row: float(row.get(time_column, "")))
        except ValueError as exc:
            raise SystemExit(f"non-numeric time value in trace '{name}'") from exc
    return grouped


def ternary_signature(values: Sequence[float], eps: float) -> Tuple[int, ...]:
    signature: List[int] = []
    for value in values:
        if value > eps:
            signature.append(1)
        elif value < -eps:
            signature.append(-1)
        else:
            signature.append(0)
    return tuple(signature)


def hamming_distance(left: Sequence[int], right: Sequence[int]) -> int:
    return sum(1 for l_i, r_i in zip(left, right) if l_i != r_i)


def magnitude_bucket(value: float, thresholds: Sequence[float]) -> int:
    magnitude = abs(value)
    bucket = 0
    for threshold in thresholds:
        if magnitude >= threshold:
            bucket += 1
    return bucket


def ultrametric_signature(values: Sequence[float], thresholds: Sequence[float]) -> Tuple[int, ...]:
    return tuple(magnitude_bucket(value, thresholds) for value in values)


def arrow_condition(delta: float, direction: str, eps: float) -> bool:
    if direction == "nondecreasing":
        return delta >= -eps
    return delta <= eps


def classify_step(structural_ok: bool, arrow_ok: bool) -> str:
    if structural_ok and arrow_ok:
        return "interior"
    if structural_ok and not arrow_ok:
        return "arrow_boundary"
    if not structural_ok and arrow_ok:
        return "structural_boundary"
    return "outside"


def execution_non_arrow_ok(record: Mapping[str, object]) -> bool:
    return (
        bool(record.get("in_cone"))
        and bool(record.get("fejer_ok"))
        and bool(record.get("basin_ok"))
        and bool(record.get("eigen_ok"))
    )


def normalize_counter(counter: Counter[str]) -> Dict[str, float]:
    total = sum(counter.values())
    if total == 0:
        return {}
    return {key: value / total for key, value in counter.items()}


def dominant_label(distribution: Dict[str, float]) -> Tuple[str, float]:
    if not distribution:
        return "<missing>", 0.0
    items = sorted(distribution.items(), key=lambda item: (-item[1], item[0]))
    return items[0]


def legacy_signature_to_eigenspace(signature: Sequence[int]) -> str:
    if not signature:
        return "Earth"
    if signature[0] > 0:
        return "Hub"
    if 0 in signature:
        return "Earth"
    return "Spoke"


def refined_signature_to_eigenspace(signature: Sequence[int]) -> str:
    if not signature:
        return "Earth"
    if signature[0] > 0:
        if len(signature) > 1 and signature[1] < 0:
            return "Spoke"
        return "Hub"
    return "Earth"


def one_hot_distribution(label: str) -> Dict[str, float]:
    if not label or label == "<missing>":
        return {}
    return {label: 1.0}


def merge_distributions(
    left: Dict[str, float],
    right: Dict[str, float],
    left_weight: float = 0.5,
    right_weight: float = 0.5,
) -> Dict[str, float]:
    if not left and not right:
        return {}
    if not left:
        return dict(right)
    if not right:
        return dict(left)
    merged: Dict[str, float] = {}
    for key in sorted(set(left) | set(right)):
        merged[key] = left_weight * left.get(key, 0.0) + right_weight * right.get(key, 0.0)
    total = sum(merged.values())
    if total == 0:
        return {}
    return {key: value / total for key, value in merged.items()}


def blend_distributions(distributions: Sequence[Dict[str, float]]) -> Dict[str, float]:
    active = [distribution for distribution in distributions if distribution]
    if not active:
        return {}
    weight = 1.0 / len(active)
    merged: Dict[str, float] = {}
    for distribution in active:
        for key, value in distribution.items():
            merged[key] = merged.get(key, 0.0) + weight * value
    total = sum(merged.values())
    if total == 0:
        return {}
    return {key: value / total for key, value in merged.items()}


def agreement_rate(left: Dict[str, str], right: Dict[str, str]) -> Tuple[int, int, float]:
    shared = sorted(set(left) & set(right))
    if not shared:
        return 0, 0, 0.0
    agreements = sum(1 for key in shared if left[key] == right[key])
    return agreements, len(shared), agreements / len(shared)


def distribution_js(left: Dict[str, float], right: Dict[str, float]) -> float:
    keys = sorted(set(left) | set(right))
    if not keys:
        return 0.0
    p = [left.get(key, 0.0) for key in keys]
    q = [right.get(key, 0.0) for key in keys]
    return jensen_shannon(p, q)


def load_jmd_index(path: Path, key_column: str) -> Dict[str, Dict[str, str]]:
    rows = load_rows(path)
    index: Dict[str, Dict[str, str]] = {}
    for row in rows:
        key = row.get(key_column, "").strip()
        if key:
            index[key] = row
    return index


def rust_array_values(text: str, name: str) -> List[str]:
    pattern = rf"{re.escape(name)}:\s*\[[^\]]+\]\s*=\s*\[(.*?)\];"
    match = re.search(pattern, text, re.DOTALL)
    if not match:
        return []
    raw = match.group(1)
    return [item.strip().strip('"') for item in raw.split(",") if item.strip()]


def rust_tuple_values(text: str, name: str) -> List[int]:
    pattern = rf"{re.escape(name)}:\s*\([^\)]*\)\s*=\s*\((.*?)\);"
    match = re.search(pattern, text)
    if not match:
        return []
    return [int(item.strip()) for item in match.group(1).split(",") if item.strip()]


def load_dasl_source_model(repo_root: Path) -> Dict[str, object]:
    dasl_path = repo_root / "src" / "dasl.rs"
    sheaf_path = repo_root / "src" / "sheaf.rs"
    ipfs_path = repo_root / "src" / "ipfs.rs"
    if not dasl_path.exists():
        raise SystemExit(f"missing DASL source file: {dasl_path}")
    if not sheaf_path.exists():
        raise SystemExit(f"missing DASL source file: {sheaf_path}")
    dasl_text = dasl_path.read_text(encoding="utf-8")
    sheaf_text = sheaf_path.read_text(encoding="utf-8")

    monster_primes = [int(item) for item in rust_array_values(dasl_text, "MONSTER_PRIMES")]
    monster_exponents = [int(item) for item in rust_array_values(dasl_text, "MONSTER_EXPONENTS")]
    bott_names = rust_array_values(dasl_text, "BOTT_NAMES")
    attack_triple = rust_tuple_values(dasl_text, "ATTACK_TRIPLE")

    encoding_names: Dict[str, str] = {}
    for variant, label in re.findall(r"Self::(\w+)\s*=>\s*\"([^\"]+)\"", sheaf_text):
        encoding_names[variant] = label

    encoding_primes: Dict[str, int] = {}
    for variant, prime_text in re.findall(r"Self::(\w+)\s*=>\s*(\d+)", sheaf_text):
        encoding_primes[variant] = int(prime_text)

    prime_to_eigenspace: Dict[int, str] = {}
    for raw_primes, eigenspace in re.findall(r"([0-9\s|]+)=>\s*EigenSpace::(\w+)", sheaf_text):
        primes = [int(item.strip()) for item in raw_primes.split("|") if item.strip()]
        for prime in primes:
            prime_to_eigenspace[prime] = eigenspace

    encoding_entries: List[Dict[str, object]] = []
    for variant in sorted(encoding_primes):
        prime = encoding_primes[variant]
        in_monster_basis = prime in monster_primes
        hecke_index = monster_primes.index(prime) if in_monster_basis else None
        bott_index = (hecke_index % len(bott_names)) if hecke_index is not None and bott_names else None
        entry = {
            "kind": "encoding",
            "encoding": variant,
            "encoding_name": encoding_names.get(variant, variant.lower()),
            "prime": prime,
            "eigenspace": prime_to_eigenspace.get(prime, "Earth"),
            "hecke": f"T_{prime}" if in_monster_basis else "<none>",
            "hecke_index": hecke_index,
            "bott_index": bott_index,
            "bott_name": bott_names[bott_index] if bott_index is not None and bott_names else "<none>",
            "attack_triple": prime in attack_triple,
            "monster_basis": in_monster_basis,
        }
        encoding_entries.append(entry)

    encoding_by_prime = {
        int(entry["prime"]): str(entry["encoding_name"])
        for entry in encoding_entries
        if bool(entry["monster_basis"])
    }

    monster_prime_entries: List[Dict[str, object]] = []
    for index, prime in enumerate(monster_primes):
        monster_prime_entries.append(
            {
                "kind": "monster-prime",
                "prime_index": index,
                "prime": prime,
                "exponent": monster_exponents[index] if index < len(monster_exponents) else None,
                "eigenspace": prime_to_eigenspace.get(prime, "Earth"),
                "hecke": f"T_{prime}",
                "hecke_index": index,
                "bott_index": index % len(bott_names) if bott_names else None,
                "bott_name": bott_names[index % len(bott_names)] if bott_names else "<none>",
                "attack_triple": prime in attack_triple,
                "monster_basis": True,
                "encoding_name": encoding_by_prime.get(prime, "<none>"),
            }
        )

    def eigenspace_distribution(selected: Sequence[Dict[str, object]]) -> Dict[str, float]:
        counter: Counter[str] = Counter(
            str(entry["eigenspace"])
            for entry in selected
            if bool(entry.get("monster_basis")) or bool(entry.get("attack_triple"))
        )
        return normalize_counter(counter)

    encoding_full_entries = [
        entry for entry in encoding_entries if bool(entry["monster_basis"]) and entry["prime"] != 1
    ]
    attack_entries = [entry for entry in monster_prime_entries if bool(entry["attack_triple"])]
    model = {
        "repo_root": str(repo_root),
        "files": {
            "dasl": str(dasl_path),
            "sheaf": str(sheaf_path),
            "ipfs": str(ipfs_path),
        },
        "monster_primes": monster_primes,
        "monster_exponents": monster_exponents,
        "attack_triple": attack_triple,
        "bott_names": bott_names,
        "entries": monster_prime_entries,
        "catalogs": {
            "encoding-prior": encoding_entries,
            "full": monster_prime_entries,
            "monster-primes": monster_prime_entries,
            "attack-triple": attack_entries,
        },
        "distributions": {
            "full": eigenspace_distribution(monster_prime_entries),
            "encoding-prior": eigenspace_distribution(encoding_full_entries),
            "monster-primes": eigenspace_distribution(monster_prime_entries),
            "attack-triple": eigenspace_distribution(attack_entries),
        },
        "counts": {
            "encoding-prior": len(encoding_full_entries),
            "monster-primes": len(monster_prime_entries),
            "attack-triple": len(attack_entries),
        },
    }
    return model


def source_catalog(model: Dict[str, object], mode: str) -> List[Dict[str, object]]:
    catalogs = model.get("catalogs", {})
    if isinstance(catalogs, dict) and mode in catalogs:
        return list(catalogs[mode])  # type: ignore[index]
    if isinstance(catalogs, dict) and "monster-primes" in catalogs:
        return list(catalogs["monster-primes"])  # type: ignore[index]
    return []


def canonical_prime_projection(
    model: Dict[str, object],
    mode: str,
    trace_label: str,
    fallback_label: str,
) -> Dict[str, object]:
    catalog = source_catalog(model, mode)
    if not catalog:
        return {
            "eigenspace": fallback_label or "<missing>",
            "prime": "",
            "hecke": "<missing>",
            "exponent": None,
            "candidate_count": 0,
            "mode": "no_source_catalog",
        }
    target_label = trace_label if any(str(entry.get("eigenspace")) == trace_label for entry in catalog) else fallback_label
    candidates = [entry for entry in catalog if str(entry.get("eigenspace")) == target_label]
    if not candidates:
        return {
            "eigenspace": target_label or "<missing>",
            "prime": "",
            "hecke": "<missing>",
            "exponent": None,
            "candidate_count": 0,
            "mode": "no_matching_eigenspace",
        }
    ranked = sorted(
        candidates,
        key=lambda entry: (
            -int(entry.get("exponent") or 0),
            int(entry.get("prime") or 0),
        ),
    )
    chosen = ranked[0]
    return {
        "eigenspace": str(chosen.get("eigenspace", target_label)),
        "prime": int(chosen.get("prime", 0)),
        "hecke": str(chosen.get("hecke", "<missing>")),
        "exponent": int(chosen.get("exponent") or 0),
        "candidate_count": len(candidates),
        "mode": "canonical_by_eigenspace_exponent",
    }


def ranked_prime_projection(
    model: Dict[str, object],
    mode: str,
    trace_distribution: Dict[str, float],
    preferred_label: str,
    canonical_projection: Dict[str, object],
    top_n: int = 3,
) -> Dict[str, object]:
    catalog = source_catalog(model, mode)
    if not catalog:
        return {
            "best": {
                "eigenspace": preferred_label or "<missing>",
                "prime": "",
                "hecke": "<missing>",
                "exponent": None,
                "score": 0.0,
                "attack_triple": False,
                "canonical_alignment": False,
                "score_components": {
                    "trace_support": 0.0,
                    "exponent_norm": 0.0,
                    "canonical_alignment": 0.0,
                    "hecke_proximity": 0.0,
                    "bott_alignment": 0.0,
                    "attack_bonus": 0.0,
                },
            },
            "top": [],
            "top_role": "diagnostic_shortlist",
            "mode": "no_source_catalog",
        }
    max_exponent = max(int(entry.get("exponent") or 0) for entry in catalog) or 1
    canonical_prime = int(canonical_projection.get("prime") or 0) if canonical_projection.get("prime") else 0
    canonical_entry = next(
        (entry for entry in catalog if int(entry.get("prime") or 0) == canonical_prime),
        None,
    )
    canonical_hecke_index = (
        int(canonical_entry.get("hecke_index"))
        if canonical_entry is not None and canonical_entry.get("hecke_index") is not None
        else None
    )
    canonical_bott_index = (
        int(canonical_entry.get("bott_index"))
        if canonical_entry is not None and canonical_entry.get("bott_index") is not None
        else None
    )
    bott_cycle = max(1, len(model.get("bott_names", [])))
    scored: List[Dict[str, object]] = []
    for entry in catalog:
        eigenspace = str(entry.get("eigenspace", "<missing>"))
        trace_support = float(trace_distribution.get(eigenspace, 0.0))
        exponent_norm = float(int(entry.get("exponent") or 0)) / float(max_exponent)
        attack_bonus = 1.0 if bool(entry.get("attack_triple")) else 0.0
        canonical_alignment = 1.0 if canonical_prime and int(entry.get("prime") or 0) == canonical_prime else 0.0
        if canonical_hecke_index is not None and entry.get("hecke_index") is not None and len(catalog) > 1:
            hecke_distance = abs(int(entry.get("hecke_index") or 0) - canonical_hecke_index)
            hecke_proximity = 1.0 - (hecke_distance / float(len(catalog) - 1))
        else:
            hecke_proximity = 0.0
        if canonical_bott_index is not None and entry.get("bott_index") is not None and bott_cycle > 1:
            bott_distance = abs(int(entry.get("bott_index") or 0) - canonical_bott_index)
            bott_circular = min(bott_distance, bott_cycle - bott_distance)
            bott_alignment = 1.0 - (bott_circular / float(bott_cycle // 2 or 1))
        else:
            bott_alignment = 0.0
        score = (
            0.40 * trace_support
            + 0.20 * exponent_norm
            + 0.15 * canonical_alignment
            + 0.15 * hecke_proximity
            + 0.05 * bott_alignment
            + 0.05 * attack_bonus
        )
        scored.append(
            {
                "eigenspace": eigenspace,
                "prime": int(entry.get("prime", 0)),
                "hecke": str(entry.get("hecke", "<missing>")),
                "exponent": int(entry.get("exponent") or 0),
                "score": score,
                "attack_triple": bool(entry.get("attack_triple")),
                "canonical_alignment": bool(canonical_alignment),
                "score_components": {
                    "trace_support": trace_support,
                    "exponent_norm": exponent_norm,
                    "canonical_alignment": canonical_alignment,
                    "hecke_proximity": hecke_proximity,
                    "bott_alignment": bott_alignment,
                    "attack_bonus": attack_bonus,
                },
            }
        )
    ranked = sorted(
        scored,
        key=lambda entry: (
            -float(entry["score"]),
            -int(bool(entry["canonical_alignment"])),
            -int(entry["exponent"]),
            -int(bool(entry["attack_triple"])),
            int(entry["prime"]),
        ),
    )
    return {
        "best": ranked[0],
        "top": ranked[:top_n],
        "top_role": "diagnostic_shortlist",
        "mode": "scored_trace_support_exponent_canonical_attack",
    }


def primary_prime_projection(
    primary_mode: str,
    canonical_projection: Dict[str, object],
    ranked_projection: Dict[str, object],
) -> Dict[str, object]:
    if primary_mode == "scored":
        best = ranked_projection.get("best", {})
        return {
            "selection_mode": "scored_primary",
            "eigenspace": str(best.get("eigenspace", canonical_projection.get("eigenspace", "<missing>"))),
            "prime": best.get("prime", canonical_projection.get("prime", "")),
            "hecke": str(best.get("hecke", canonical_projection.get("hecke", "<missing>"))),
            "exponent": best.get("exponent", canonical_projection.get("exponent")),
            "score": float(best.get("score", 0.0)),
            "score_components": dict(best.get("score_components", {})),
        }
    return {
        "selection_mode": "canonical_primary",
        "eigenspace": str(canonical_projection.get("eigenspace", "<missing>")),
        "prime": canonical_projection.get("prime", ""),
        "hecke": str(canonical_projection.get("hecke", "<missing>")),
        "exponent": canonical_projection.get("exponent"),
        "score": float(ranked_projection.get("best", {}).get("score", 0.0)),
        "score_components": dict(ranked_projection.get("best", {}).get("score_components", {})),
    }


def emit_dasl_source_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def classify_step_constructor_name(status_class: str) -> str:
    mapping = {
        "interior": "Interior",
        "arrow_boundary": "ArrowBoundary",
        "structural_boundary": "StructuralBoundary",
        "outside": "Outside",
    }
    return mapping[status_class]


def classify_family_constructor_name(family_class: str) -> str:
    mapping = {
        "interior_family": "InteriorFamily",
        "arrow_ladder": "ArrowLadderFamily",
        "single_arrow_break": "SingleArrowBreakFamily",
        "mdl_tail_boundary": "MDLTailBoundaryFamily",
        "mixed_hard_axis_outlier": "MDLTailBoundaryFamily",
    }
    return mapping[family_class]


def bool_set_constructor(value: bool) -> str:
    return "⊤" if value else "⊥"


def fin_pattern(index: int) -> str:
    pattern = "zero"
    for _ in range(index):
        pattern = f"(suc {pattern})"
    return pattern


def agda_module_name_from_path(path: Path) -> str:
    rel = path.resolve().relative_to(ROOT_DIR.resolve()).with_suffix("")
    return ".".join(rel.parts)


def emit_execution_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def emit_json(path: Path, payload: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def format_score_components(components: Dict[str, object]) -> str:
    if not components:
        return "{}"
    ordered_keys = [
        "trace_support",
        "exponent_norm",
        "canonical_alignment",
        "hecke_proximity",
        "bott_alignment",
        "attack_bonus",
    ]
    parts: List[str] = []
    for key in ordered_keys:
        value = components.get(key)
        if value is None:
            continue
        parts.append(f"{key}={float(value):.4f}")
    return ", ".join(parts) if parts else "{}"


def classify_arrow_boundary_family(
    base_family_class: str,
    family_context: Dict[str, object] | None,
) -> Tuple[str, str]:
    if not isinstance(family_context, dict):
        return base_family_class, "no_family_context"
    tail_summary = family_context.get("tail_summary")
    report_summary = family_context.get("report_summary")
    if not isinstance(tail_summary, dict) or not isinstance(report_summary, dict):
        return base_family_class, "missing_tail_or_report_summary"
    closest_rows = report_summary.get("closestpoint")
    fejer_rows = report_summary.get("fejer_set")
    mdl_rows = report_summary.get("mdl_descent")
    if not (isinstance(closest_rows, list) and closest_rows and isinstance(fejer_rows, list) and fejer_rows):
        return base_family_class, "missing_closestpoint_or_fejer_rows"
    if not (isinstance(mdl_rows, list) and mdl_rows):
        return base_family_class, "missing_mdl_rows"
    closest_ok = all(float(row.get("closest_frac", 0.0)) >= 1.0 for row in closest_rows)
    fejer_ok = all(float(row.get("fejer_set_frac", 0.0)) >= 1.0 for row in fejer_rows)
    mdl_bad = any(not bool(row.get("MDL_monotone", False)) for row in mdl_rows)
    tail_heavy = bool(tail_summary.get("tail_has_max_fractional_uncertainty"))
    if base_family_class == "mixed_hard_axis_outlier" and closest_ok and fejer_ok and mdl_bad and tail_heavy:
        return (
            "mdl_tail_boundary",
            "mixed_hard_axis_outlier + closestpoint/fejer admissible + mdl_exact_fail + tail_max_frac_err",
        )
    return base_family_class, "no_exception_override"


def summarize_arrow_boundary_families(
    records: Sequence[Dict[str, object]],
    family_contexts: Dict[str, Dict[str, object]] | None = None,
) -> List[Dict[str, object]]:
    grouped: Dict[str, List[Dict[str, object]]] = defaultdict(list)
    for record in records:
        if str(record.get("status_class")) == "arrow_boundary":
            grouped[str(record["name"])].append(record)
    summaries: List[Dict[str, object]] = []
    for name in sorted(grouped):
        subset = sorted(grouped[name], key=lambda record: (float(record["t"]), float(record["next_t"])))
        eps_values = [abs(float(record["arrow_delta"])) for record in subset]
        failure_counts: Counter[str] = Counter()
        signature_counts: Counter[str] = Counter()
        for record in subset:
            for column in record["cone_failures"]:
                failure_counts[column] += 1
            signature_counts[",".join(str(item) for item in record["structural_signature"])] += 1
        non_arrow_failures = {axis: count for axis, count in failure_counts.items() if axis != "v_arrow"}
        profile_clearance = {
            profile: all(abs(float(record["arrow_delta"])) <= eps for record in subset)
            for profile, eps in ARROW_PROFILES.items()
        }
        if non_arrow_failures:
            base_family_class = "mixed_hard_axis_outlier"
        elif len(subset) == 1:
            base_family_class = "single_arrow_break"
        else:
            base_family_class = "arrow_ladder"
        family_context = family_contexts.get(name) if family_contexts else None
        family_class, class_reason = classify_arrow_boundary_family(base_family_class, family_context)
        summaries.append(
            {
                "name": name,
                "count": len(subset),
                "min_required_eps": min(eps_values) if eps_values else 0.0,
                "max_required_eps": max(eps_values) if eps_values else 0.0,
                "mean_required_eps": mean(eps_values),
                "failure_axes": dict(failure_counts),
                "non_arrow_failures": non_arrow_failures,
                "profile_clearance": profile_clearance,
                "family_class_base": base_family_class,
                "family_class": family_class,
                "family_class_reason": class_reason,
                "top_structural_signatures": dict(signature_counts.most_common(3)),
                "step_pairs": [
                    {
                        "t": record["t"],
                        "next_t": record["next_t"],
                        "arrow_delta": float(record["arrow_delta"]),
                        "energy_delta": float(record["energy_delta"]),
                    }
                    for record in subset
                ],
            }
        )
    return summaries


def infer_dashifine_context_root(input_path: Path) -> Path | None:
    resolved = input_path.resolve()
    for parent in resolved.parents:
        if parent.name == "dashifine":
            return parent
    return None


def infer_dashifine_family_dirs(input_path: Path, context_root: Path) -> Tuple[Path, Path]:
    input_text = str(input_path)
    if "hepdata_lyapunov_test_out_new" in input_text:
        return (
            context_root / "hepdata_to_dashi_new",
            context_root / "hepdata_npz_all",
        )
    if "hepdata_lyapunov_test_out_all" in input_text:
        return (
            context_root / "hepdata_to_dashi_all",
            context_root / "hepdata_npz_all",
        )
    return (
        context_root / "hepdata_to_dashi",
        context_root / "hepdata_npz",
    )


def infer_dashifine_report_dir(input_path: Path, context_root: Path) -> Path | None:
    input_text = str(input_path)
    if "hepdata_lyapunov_test_out_new" in input_text:
        return context_root / "hepdata_lyapunov_test_out_new" / "dashi_idk_out"
    if "hepdata_lyapunov_test_out_all" in input_text:
        return context_root / "hepdata_lyapunov_test_out_all" / "dashi_idk_out"
    if "hepdata_lyapunov_test_out" in input_text:
        return context_root / "hepdata_lyapunov_test_out" / "dashi_idk_out.csv"
    return None


def read_csv_row_by_label(path: Path, label: str) -> List[Dict[str, str]]:
    if not path.exists():
        return []
    with path.open("r", encoding="utf-8", newline="") as fh:
        reader = csv.DictReader(fh)
        return [row for row in reader if row.get("label") == label]


def load_dashifine_family_context(input_path: Path, family_name: str) -> Dict[str, object] | None:
    context_root = infer_dashifine_context_root(input_path)
    if context_root is None:
        return None
    lens_root, npz_root = infer_dashifine_family_dirs(input_path, context_root)
    report_root = infer_dashifine_report_dir(input_path, context_root)
    meta_path = lens_root / family_name / "meta.txt"
    metrics_path = context_root / "hepdata_dashi_native" / f"{family_name}_dashi_native_metrics.csv"
    npz_path = npz_root / f"{family_name}.npz"
    if not npz_path.exists():
        fallback_npz = context_root / "hepdata_npz" / f"{family_name}.npz"
        if fallback_npz.exists():
            npz_path = fallback_npz

    payload: Dict[str, object] = {
        "family": family_name,
        "context_root": str(context_root),
        "meta_path": str(meta_path) if meta_path.exists() else None,
        "metrics_path": str(metrics_path) if metrics_path.exists() else None,
        "npz_path": str(npz_path) if npz_path.exists() else None,
    }

    if meta_path.exists():
        meta: Dict[str, float | str] = {}
        for line in meta_path.read_text(encoding="utf-8").splitlines():
            if "=" not in line:
                continue
            key, value = line.split("=", 1)
            key = key.strip()
            value = value.strip()
            try:
                meta[key] = float(value)
            except ValueError:
                meta[key] = value
        payload["meta"] = meta

    if metrics_path.exists():
        with metrics_path.open("r", encoding="utf-8", newline="") as fh:
            reader = csv.DictReader(fh)
            metrics_rows = list(reader)
        payload["metrics"] = [
            {
                "iter": int(float(row["iter"])),
                "alpha": float(row["alpha"]),
                "chi2": float(row["chi2"]),
                "chi2_dof": float(row["chi2_dof"]),
                "odd_even_ratio": float(row["odd_even_ratio"]),
                "R_E_hi": float(row["R_E_hi"]),
                "condA": float(row["condA"]),
            }
            for row in metrics_rows
        ]

    if npz_path.exists():
        try:
            import numpy as np  # type: ignore

            npz = np.load(npz_path, allow_pickle=True)
            x = [float(value) for value in npz["x"].tolist()]
            y = [float(value) for value in npz["y"].tolist()]
            cov = npz["cov"]
            diag = [float(cov[idx][idx]) for idx in range(len(y))]
            err = [math.sqrt(max(value, 0.0)) for value in diag]
            frac_err = [abs(err_i / y_i) if y_i != 0.0 else math.inf for err_i, y_i in zip(err, y)]
            max_frac_idx = max(range(len(frac_err)), key=lambda idx: frac_err[idx])
            tail_count = min(3, len(x))
            payload["observable_bins"] = [
                {
                    "bin_index": idx,
                    "x": x[idx],
                    "y": y[idx],
                    "err": err[idx],
                    "frac_err": frac_err[idx],
                }
                for idx in range(len(x))
            ]
            payload["tail_bins"] = [
                {
                    "bin_index": idx,
                    "x": x[idx],
                    "y": y[idx],
                    "err": err[idx],
                    "frac_err": frac_err[idx],
                }
                for idx in range(len(x) - tail_count, len(x))
            ]
            payload["tail_summary"] = {
                "bin_count": len(x),
                "max_frac_err_bin": max_frac_idx,
                "max_frac_err_x": x[max_frac_idx],
                "max_frac_err_value": frac_err[max_frac_idx],
                "last_bin_x": x[-1],
                "last_bin_frac_err": frac_err[-1],
                "tail_has_max_fractional_uncertainty": max_frac_idx == len(x) - 1,
            }
        except Exception as exc:
            payload["npz_error"] = str(exc)

    if report_root is not None:
        closest_rows = read_csv_row_by_label(report_root / "closestpoint_report.csv", family_name)
        fejer_rows = read_csv_row_by_label(report_root / "fejer_set_report.csv", family_name)
        mdl_rows = read_csv_row_by_label(report_root / "mdl_descent_exact.csv", family_name)
        defect_rows = read_csv_row_by_label(report_root / "defect_monotonicity_report.csv", family_name)
        report_summary: Dict[str, object] = {}
        if closest_rows:
            report_summary["closestpoint"] = [
                {
                    "metric": row["metric"],
                    "closest_frac": float(row["closest_frac"]),
                    "closest_max_violation": float(row["closest_max_violation"]),
                    "closest_argmax": int(float(row["closest_argmax"])),
                    "T_iter": int(float(row["T_iter"])),
                    "beta_dim": int(float(row["beta_dim"])),
                }
                for row in closest_rows
            ]
        if fejer_rows:
            report_summary["fejer_set"] = [
                {
                    "metric": row["metric"],
                    "fejer_set_frac": float(row["fejer_set_frac"]),
                    "fejer_set_max_violation": float(row["fejer_set_max_violation"]),
                    "fejer_set_argmax": int(float(row["fejer_set_argmax"])),
                    "T_iter": int(float(row["T_iter"])),
                    "beta_dim": int(float(row["beta_dim"])),
                }
                for row in fejer_rows
            ]
        if mdl_rows:
            report_summary["mdl_descent"] = [
                {
                    "MDL_monotone": row["MDL_monotone"] == "True",
                    "MDL_violations": int(float(row["MDL_violations"])),
                    "MDL_worst_increase": float(row["MDL_worst_increase"]),
                    "MDL_worst_iter": int(float(row["MDL_worst_iter"])),
                    "T_iter": int(float(row["T_iter"])),
                }
                for row in mdl_rows
            ]
        if defect_rows:
            report_summary["defect_monotonicity"] = [
                {
                    "L1_monotone": row["L1_monotone"] == "True",
                    "L1_violations": int(float(row["L1_violations"])),
                    "L1_worst_increase": float(row["L1_worst_increase"]),
                    "L2_monotone": row["L2_monotone"] == "True",
                    "L2_violations": int(float(row["L2_violations"])),
                    "L2_worst_increase": float(row["L2_worst_increase"]),
                    "T_iter": int(float(row["T_iter"])),
                    "beta_dim": int(float(row["beta_dim"])),
                }
                for row in defect_rows
            ]
        if report_summary:
            payload["report_summary"] = report_summary

    return payload


def build_family_drilldown(
    records: Sequence[Dict[str, object]],
    family_name: str,
    family_context: Dict[str, object] | None = None,
) -> Dict[str, object]:
    subset = [record for record in records if str(record["name"]) == family_name]
    subset.sort(key=lambda record: (float(record["t"]), float(record["next_t"])))
    boundary_subset = [record for record in subset if str(record.get("status_class")) == "arrow_boundary"]
    v_dnorm_pairs = [
        (
            float(record.get("axis_values", {}).get("v_dnorm")),
            float(record.get("next_axis_values", {}).get("v_dnorm")),
        )
        for record in subset
        if isinstance(record.get("axis_values"), dict)
        and isinstance(record.get("next_axis_values"), dict)
        and record.get("axis_values", {}).get("v_dnorm") is not None
        and record.get("next_axis_values", {}).get("v_dnorm") is not None
    ]
    alt_v_dnorm = None
    if v_dnorm_pairs:
        v_dnorm_values = [value for pair in v_dnorm_pairs for value in pair]
        sorted_values = sorted(v_dnorm_values)
        mid = len(sorted_values) // 2
        median = (
            sorted_values[mid]
            if len(sorted_values) % 2 == 1
            else 0.5 * (sorted_values[mid - 1] + sorted_values[mid])
        )
        deviations = sorted(abs(value - median) for value in v_dnorm_values)
        mad = deviations[len(deviations) // 2] if deviations else 0.0
        clip_index = min(len(sorted_values) - 1, max(0, int(0.95 * (len(sorted_values) - 1))))
        clip_hi = sorted_values[clip_index]
        min_v = min(v_dnorm_values)
        max_v = max(v_dnorm_values)

        def transform_value(kind: str, value: float) -> float:
            if kind == "raw":
                return value
            if kind == "log_abs":
                return math.log1p(abs(value))
            if kind == "robust_z":
                return ((value - median) / mad) if mad > 0 else 0.0
            if kind == "winsor95":
                return min(value, clip_hi)
            if kind == "family_minmax":
                return ((value - min_v) / (max_v - min_v)) if max_v > min_v else 0.0
            raise ValueError(f"unknown transform kind: {kind}")

        alt_v_dnorm = {
            kind: {
                "boundary_failures": [
                    {
                        "t": record["t"],
                        "next_t": record["next_t"],
                        "value": transform_value(kind, float(record["axis_values"]["v_dnorm"])),
                        "next_value": transform_value(kind, float(record["next_axis_values"]["v_dnorm"])),
                        "delta": transform_value(kind, float(record["next_axis_values"]["v_dnorm"]))
                        - transform_value(kind, float(record["axis_values"]["v_dnorm"])),
                        "nonincreasing_ok": (
                            transform_value(kind, float(record["next_axis_values"]["v_dnorm"]))
                            - transform_value(kind, float(record["axis_values"]["v_dnorm"]))
                        )
                        <= 0.0,
                    }
                    for record in subset
                    if str(record.get("status_class")) == "arrow_boundary"
                ],
                "all_step_deltas": [
                    {
                        "t": record["t"],
                        "next_t": record["next_t"],
                        "delta": transform_value(kind, float(record["next_axis_values"]["v_dnorm"]))
                        - transform_value(kind, float(record["axis_values"]["v_dnorm"])),
                    }
                    for record in subset
                ],
            }
            for kind in ("raw", "log_abs", "robust_z", "winsor95", "family_minmax")
        }
    onset = None
    if boundary_subset:
        first_boundary = boundary_subset[0]
        first_index = subset.index(first_boundary)
        previous_record = subset[first_index - 1] if first_index > 0 else None
        onset = {
            "first_boundary_index": first_index,
            "first_boundary_t": first_boundary["t"],
            "first_boundary_next_t": first_boundary["next_t"],
            "first_boundary_failures": list(first_boundary["cone_failures"]),
            "first_boundary_arrow_delta": float(first_boundary["arrow_delta"]),
            "first_boundary_energy_delta": float(first_boundary["energy_delta"]),
            "first_boundary_signature": list(first_boundary["structural_signature"]),
            "previous_t": previous_record["t"] if previous_record is not None else None,
            "previous_next_t": previous_record["next_t"] if previous_record is not None else None,
            "previous_arrow_delta": float(previous_record["arrow_delta"]) if previous_record is not None else None,
            "previous_energy_delta": float(previous_record["energy_delta"]) if previous_record is not None else None,
            "previous_signature": list(previous_record["structural_signature"]) if previous_record is not None else None,
            "signature_changed": (
                list(previous_record["structural_signature"]) != list(first_boundary["structural_signature"])
                if previous_record is not None
                else False
            ),
            "arrow_sign_flip": (
                float(previous_record["arrow_delta"]) <= 0.0 < float(first_boundary["arrow_delta"])
                if previous_record is not None
                else False
            ),
            "failure_mode": (
                "mixed_hard_axis"
                if any(axis != "v_arrow" for axis in first_boundary["cone_failures"])
                else "arrow_only"
            ),
        }
    return {
        "name": family_name,
        "step_count": len(subset),
        "boundary_count": len(boundary_subset),
        "boundary_summary": summarize_arrow_boundary_families(
            subset,
            {family_name: family_context} if family_context is not None else None,
        ),
        "family_context": family_context,
        "alt_v_dnorm": alt_v_dnorm,
        "onset": onset,
        "records": [
            {
                "t": record["t"],
                "next_t": record["next_t"],
                "status_class": record["status_class"],
                "cone_failures": list(record["cone_failures"]),
                "structural_signature": list(record["structural_signature"]),
                "structural_ultra": list(record["structural_ultra"]),
                "structural_radius": record["structural_radius"],
                "arrow_delta": float(record["arrow_delta"]),
                "energy_delta": float(record["energy_delta"]),
                "delta_norm": float(record["delta_norm"]),
                "structural_ok": bool(record["structural_ok"]),
                "cone_ok": bool(record.get("cone_ok", record["in_cone"])),
                "mdl_ok": bool(record.get("mdl_ok", record["fejer_ok"])),
                "arrow_ok": bool(record["arrow_ok"]),
                "execution_non_arrow_ok": bool(record.get("execution_non_arrow_ok", False)),
                "joint_ok": bool(record["joint_ok"]),
                "legacy_joint_ok": bool(record.get("legacy_joint_ok", False)),
                "legacy_status_class": str(record.get("legacy_status_class", record["status_class"])),
                "trace_eigenspace": record["trace_eigenspace"],
                "source_projection_eigenspace": record["source_projection_eigenspace"],
                "source_projection_prime": record["source_projection_prime"],
                "axis_values": dict(record.get("axis_values", {})),
                "next_axis_values": dict(record.get("next_axis_values", {})),
                "delta_by_axis": dict(record.get("delta_by_axis", {})),
            }
            for record in subset
        ],
    }


def all_report_rows_satisfy(
    report_summary: Dict[str, object] | None,
    key: str,
    predicate,
) -> bool | None:
    if not isinstance(report_summary, dict):
        return None
    rows = report_summary.get(key)
    if not isinstance(rows, list) or not rows:
        return None
    try:
        return all(predicate(row) for row in rows)
    except Exception:
        return None


def build_family_classification_records(
    trace_records: Dict[str, List[Dict[str, object]]],
    family_summaries: Sequence[Dict[str, object]],
    family_contexts: Dict[str, Dict[str, object]],
) -> List[Dict[str, object]]:
    summary_by_name = {str(summary["name"]): summary for summary in family_summaries}
    rows: List[Dict[str, object]] = []
    for name in sorted(trace_records):
        subset = trace_records[name]
        summary = summary_by_name.get(name)
        family_context = family_contexts.get(name)
        report_summary = (
            family_context.get("report_summary") if isinstance(family_context, dict) else None
        )
        tail_summary = family_context.get("tail_summary") if isinstance(family_context, dict) else None
        family_class = str(summary["family_class"]) if summary else "interior_family"
        family_class_base = str(summary["family_class_base"]) if summary else "interior_family"
        family_class_reason = (
            str(summary["family_class_reason"]) if summary else "no_boundary_steps"
        )
        boundary_indices = [
            index
            for index, record in enumerate(subset)
            if str(record.get("status_class")) == "arrow_boundary"
        ]
        first_boundary_index = boundary_indices[0] if boundary_indices else None
        terminal_boundary = (
            (first_boundary_index / max(1, len(subset) - 1)) >= 0.75
            if first_boundary_index is not None
            else None
        )
        cone_ok = all(bool(record.get("cone_ok", record.get("in_cone"))) for record in subset)
        closest_ok = all_report_rows_satisfy(
            report_summary,
            "closestpoint",
            lambda row: float(row["closest_frac"]) >= 1.0,
        )
        fejer_ok = all_report_rows_satisfy(
            report_summary,
            "fejer_set",
            lambda row: float(row["fejer_set_frac"]) >= 1.0,
        )
        mdl_exact_ok = all_report_rows_satisfy(
            report_summary,
            "mdl_descent",
            lambda row: bool(row["MDL_monotone"]),
        )
        tail_localized = (
            bool(tail_summary.get("tail_has_max_fractional_uncertainty"))
            if isinstance(tail_summary, dict)
            else None
        )
        rows.append(
            {
                "family": name,
                "family_class": family_class,
                "family_class_base": family_class_base,
                "family_class_reason": family_class_reason,
                "cone_ok": cone_ok,
                "fejer_ok": fejer_ok,
                "closest_ok": closest_ok,
                "mdl_exact_ok": mdl_exact_ok,
                "tail_localized": tail_localized,
                "terminal_boundary": terminal_boundary,
                "first_boundary_index": first_boundary_index,
                "boundary_steps": sum(
                    1 for record in subset if str(record.get("status_class")) == "arrow_boundary"
                ),
                "step_count": len(subset),
            }
        )
    return rows


def summarize_tail_boundary_lemma(rows: Sequence[Dict[str, object]]) -> Dict[str, object]:
    class_counts = Counter(str(row["family_class"]) for row in rows)
    mdl_rows = [row for row in rows if str(row["family_class"]) == "mdl_tail_boundary"]

    def counts_by_class(flag: str) -> Dict[str, int]:
        counter: Counter[str] = Counter()
        for row in rows:
            if row.get(flag) is True:
                counter[str(row["family_class"])] += 1
        return dict(sorted(counter.items()))

    return {
        "family_count": len(rows),
        "class_counts": dict(sorted(class_counts.items())),
        "mdl_tail_boundary_count": len(mdl_rows),
        "mdl_tail_boundary_families": [str(row["family"]) for row in mdl_rows],
        "mdl_tail_boundary_all_cone_ok": all(bool(row.get("cone_ok")) for row in mdl_rows) if mdl_rows else None,
        "mdl_tail_boundary_all_fejer_ok": all(bool(row.get("fejer_ok")) for row in mdl_rows) if mdl_rows else None,
        "mdl_tail_boundary_all_closest_ok": all(bool(row.get("closest_ok")) for row in mdl_rows) if mdl_rows else None,
        "mdl_tail_boundary_all_mdl_exact_fail": all(not bool(row.get("mdl_exact_ok")) for row in mdl_rows) if mdl_rows else None,
        "mdl_tail_boundary_all_tail_localized": all(row.get("tail_localized") is True for row in mdl_rows) if mdl_rows else None,
        "mdl_tail_boundary_all_terminal_boundary": all(row.get("terminal_boundary") is True for row in mdl_rows) if mdl_rows else None,
        "tail_localized_counts_by_class": counts_by_class("tail_localized"),
        "terminal_boundary_counts_by_class": counts_by_class("terminal_boundary"),
    }


def emit_tail_boundary_summary_json(path: Path, summary: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def emit_eigen_csv(path: Path, rows: Sequence[Dict[str, object]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    fieldnames = [
        "name",
        "group",
        "step_count",
        "legacy_trace_eigenspace",
        "legacy_trace_score",
        "trace_eigenspace",
        "trace_score",
        "jmd_eigenspace",
        "jmd_score",
        "dasl_eigenspace",
        "dasl_score",
        "hybrid_eigenspace",
        "hybrid_score",
        "basin_projection",
        "basin_support",
        "basin_js",
        "source_support_projection",
        "source_support",
        "source_support_js",
        "source_support_ok",
        "source_support_mode",
        "source_projection_eigenspace",
        "source_projection_prime",
        "source_projection_hecke",
        "source_projection_exponent",
        "source_projection_candidates",
        "source_projection_mode",
        "source_projection_score",
        "source_projection_score_components",
        "source_projection_top_role",
        "source_projection_top",
        "primary_source_projection_mode",
        "primary_source_projection_eigenspace",
        "primary_source_projection_prime",
        "primary_source_projection_hecke",
        "primary_source_projection_exponent",
        "primary_source_projection_score",
        "primary_source_projection_score_components",
        "projection_conflict",
        "projection_conflict_detail",
        "basin_ok",
        "selected_source",
        "selected_eigenspace",
        "selected_score",
        "jmd_coverage",
        "dasl_coverage",
    ]
    with path.open("w", encoding="utf-8", newline="") as fh:
        writer = csv.DictWriter(fh, fieldnames=fieldnames)
        writer.writeheader()
        for row in rows:
            writer.writerow(row)


def emit_family_classification_json(path: Path, rows: Sequence[Dict[str, object]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(list(rows), indent=2, sort_keys=True) + "\n", encoding="utf-8")


def emit_agda_family_witness(
    path: Path,
    module_name: str,
    rows: Sequence[Dict[str, object]],
) -> None:
    sorted_rows = sorted(rows, key=lambda row: str(row["family"]))
    lines: List[str] = [
        f"module {module_name} where",
        "",
        "open import Data.Unit using (⊤; tt)",
        "open import Data.Empty using (⊥)",
        "open import Data.Fin using (Fin; zero; suc)",
        "open import Agda.Builtin.Nat using (Nat)",
        "",
        "open import DASHI.Physics.Closure.ExecutionAdmissibilityWitness as EAW",
        "",
        "familyCount : Nat",
        f"familyCount = {len(sorted_rows)}",
        "",
        "TraceFamilyId : Set",
        "TraceFamilyId = Fin familyCount",
        "",
        "familyClassFn : TraceFamilyId → EAW.FamilyClass",
    ]
    for index, row in enumerate(sorted_rows):
        lines.append(
            f"familyClassFn {fin_pattern(index)} = EAW.{classify_family_constructor_name(str(row['family_class']))}"
        )
    for field_name, fn_name in (
        ("cone_ok", "coneOKFn"),
        ("fejer_ok", "fejerOKFn"),
        ("closest_ok", "closestOKFn"),
        ("mdl_exact_ok", "mdlExactOKFn"),
        ("tail_localized", "tailLocalizedFn"),
    ):
        lines.extend(["", f"{fn_name} : TraceFamilyId → Set"])
        for index, row in enumerate(sorted_rows):
            value = bool(row[field_name])
            lines.append(f"{fn_name} {fin_pattern(index)} = {bool_set_constructor(value)}")
    lines.extend(
        [
            "",
            "currentFamilyClassification : EAW.SomeFamilyClassificationWitness",
            "currentFamilyClassification =",
            "  record",
            "    { FamilyId = TraceFamilyId",
            "    ; witness =",
            "        record",
            "          { familyClass = familyClassFn",
            "          ; coneOK = coneOKFn",
            "          ; fejerOK = fejerOKFn",
            "          ; closestOK = closestOKFn",
            "          ; mdlExactOK = mdlExactOKFn",
            "          ; tailLocalized = tailLocalizedFn",
            "          }",
            "    }",
        ]
    )
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def emit_agda_witness(
    path: Path,
    module_name: str,
    records: Sequence[Dict[str, object]],
) -> None:
    sorted_records = sorted(records, key=lambda record: (str(record["name"]), float(str(record["t"]))))
    lines: List[str] = [
        f"module {module_name} where",
        "",
        "open import Data.Empty using (⊥)",
        "open import Data.Sum using (_⊎_; inj₁; inj₂)",
        "open import Data.Unit using (⊤; tt)",
        "open import Data.Fin using (Fin; zero; suc)",
        "open import Agda.Builtin.Nat using (Nat)",
        "open import Relation.Binary.PropositionalEquality using (_≡_; refl)",
        "",
        "open import DASHI.Physics.Closure.ExecutionAdmissibilityWitness as EAW",
        "",
        "stepCount : Nat",
        f"stepCount = {len(sorted_records)}",
        "",
        "TraceStepId : Set",
        "TraceStepId = Fin stepCount",
        "",
        "stepClassFn : TraceStepId → EAW.StepClass",
    ]
    for index, record in enumerate(sorted_records):
        lines.append(
            f"stepClassFn {fin_pattern(index)} = EAW.{classify_step_constructor_name(str(record['status_class']))}"
        )
    lines.extend(
        [
            "",
            "coneOKFn : TraceStepId → Set",
        ]
    )
    for index, record in enumerate(sorted_records):
        lines.append(f"coneOKFn {fin_pattern(index)} = {bool_set_constructor(bool(record.get('cone_ok', record['in_cone'])))}")
    lines.extend(
        [
            "",
            "arrowOKFn : TraceStepId → Set",
        ]
    )
    for index, record in enumerate(sorted_records):
        lines.append(f"arrowOKFn {fin_pattern(index)} = {bool_set_constructor(bool(record['arrow_ok']))}")
    lines.extend(
        [
            "",
            "mdlOKFn : TraceStepId → Set",
        ]
    )
    for index, record in enumerate(sorted_records):
        lines.append(f"mdlOKFn {fin_pattern(index)} = {bool_set_constructor(bool(record.get('mdl_ok', record['fejer_ok'])))}")
    lines.extend(
        [
            "",
            "basinOKFn : TraceStepId → Set",
        ]
    )
    for index, record in enumerate(sorted_records):
        lines.append(f"basinOKFn {fin_pattern(index)} = {bool_set_constructor(bool(record['basin_ok']))}")
    lines.extend(
        [
            "",
            "eigenOKFn : TraceStepId → Set",
        ]
    )
    for index, record in enumerate(sorted_records):
        lines.append(f"eigenOKFn {fin_pattern(index)} = {bool_set_constructor(bool(record['eigen_ok']))}")
    lines.extend(
        [
            "",
            "interiorOrBoundaryFn : (step : TraceStepId) → stepClassFn step ≡ EAW.Interior ⊎ stepClassFn step ≡ EAW.ArrowBoundary",
        ]
    )
    for index, record in enumerate(sorted_records):
        constructor = classify_step_constructor_name(str(record["status_class"]))
        if constructor == "Interior":
            proof = "inj₁ refl"
        elif constructor == "ArrowBoundary":
            proof = "inj₂ refl"
        else:
            proof = "inj₁ refl"
        lines.append(f"interiorOrBoundaryFn {fin_pattern(index)} = {proof}")
    lines.extend(
        [
            "",
            "noStructuralEscapeFn : (step : TraceStepId) → stepClassFn step ≡ EAW.StructuralBoundary ⊎ stepClassFn step ≡ EAW.Outside → ⊥",
        ]
    )
    for index, _record in enumerate(sorted_records):
        lines.append(f"noStructuralEscapeFn {fin_pattern(index)} (inj₁ ())")
        lines.append(f"noStructuralEscapeFn {fin_pattern(index)} (inj₂ ())")
    lines.extend(
        [
            "",
            "currentTraceExecutionAdmissibility : EAW.SomeExecutionAdmissibilityWitness",
            "currentTraceExecutionAdmissibility =",
            "  record",
            "    { StepId = TraceStepId",
            "    ; witness =",
            "        record",
            "          { stepClass = stepClassFn",
            "          ; coneOK = coneOKFn",
            "          ; arrowOK = arrowOKFn",
            "          ; mdlOK = mdlOKFn",
            "          ; basinOK = basinOKFn",
            "          ; eigenOK = eigenOKFn",
            "          ; interiorOrBoundary = interiorOrBoundaryFn",
            "          ; noStructuralEscape = noStructuralEscapeFn",
            "          }",
            "    }",
            "",
        ]
    )
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines), encoding="utf-8")


def naive_bayes_loo_accuracy(
    rows: Sequence[Dict[str, str]],
    categorical_features: Sequence[str],
    group_column: str,
    labels: Sequence[str],
) -> Dict[str, object]:
    correct = 0
    predictions: List[Dict[str, str]] = []
    label_set = sorted(set(labels))
    for index, test_row in enumerate(rows):
        train_rows = [row for i, row in enumerate(rows) if i != index]
        class_rows: Dict[str, List[Dict[str, str]]] = {
            label: [row for row in train_rows if row[group_column] == label] for label in label_set
        }
        vocab: Dict[str, List[str]] = {}
        for feature in categorical_features:
            values = sorted(
                {
                    row.get(feature, "").strip() or "<missing>"
                    for row in train_rows
                }
            )
            vocab[feature] = values or ["<missing>"]
        best_label = None
        best_score = -float("inf")
        for label in label_set:
            members = class_rows[label]
            prior = math.log((len(members) + 1) / (len(train_rows) + len(label_set)))
            score = prior
            for feature in categorical_features:
                value = test_row.get(feature, "").strip() or "<missing>"
                numerator = sum(
                    1 for row in members if (row.get(feature, "").strip() or "<missing>") == value
                ) + 1
                denominator = len(members) + len(vocab[feature])
                score += math.log(numerator / denominator)
            if score > best_score:
                best_score = score
                best_label = label
        actual = test_row[group_column]
        if best_label == actual:
            correct += 1
        predictions.append(
            {
                "name": test_row.get("name", f"row_{index}"),
                "actual": actual,
                "predicted": best_label or "",
            }
        )
    return {
        "accuracy": correct / len(rows),
        "rows": predictions,
    }


def occupancy_mode(args: argparse.Namespace) -> int:
    rows = load_rows(Path(args.input))
    categorical = parse_csv_list(args.categorical, DEFAULT_CATEGORICAL)
    numeric = parse_csv_list(args.numeric, DEFAULT_NUMERIC)
    joint = parse_csv_list(args.joint, DEFAULT_JOINT)
    require_columns(rows, [args.group_column, *categorical, *joint])
    monster_rows, control_rows = split_groups(
        rows, args.group_column, args.monster_label, args.control_label
    )
    analysis_rows = monster_rows + control_rows
    labels = [row[args.group_column] for row in analysis_rows]

    result: Dict[str, object] = {
        "input": args.input,
        "mode": "occupancy",
        "group_column": args.group_column,
        "monster_label": args.monster_label,
        "control_label": args.control_label,
        "monster_count": len(monster_rows),
        "control_count": len(control_rows),
        "categorical": [],
        "numeric": [],
    }

    print(f"input: {args.input}")
    print(
        f"groups: {args.monster_label}={len(monster_rows)} "
        f"{args.control_label}={len(control_rows)}"
    )
    print()

    for feature in categorical:
        monster_counts = count_values(monster_rows, feature)
        control_counts = count_values(control_rows, feature)
        keys, pm, po = aligned_probabilities(monster_counts, control_counts)
        js = jensen_shannon(pm, po)
        p_value = permutation_p_value(
            analysis_rows,
            labels,
            lambda subset, feature=feature: count_values(subset, feature),
            args.group_column,
            args.monster_label,
            args.control_label,
            args.permutations,
            args.seed,
        )
        item = {
            "feature": feature,
            "monster_counts": dict(monster_counts),
            "control_counts": dict(control_counts),
            "jensen_shannon": js,
            "permutation_p_value": p_value,
        }
        result["categorical"].append(item)
        print(f"[categorical] {feature}")
        print(f"  {args.monster_label}: {format_counts(monster_counts, args.top_n)}")
        print(f"  {args.control_label}: {format_counts(control_counts, args.top_n)}")
        print(f"  JS={js:.4f} perm_p={p_value:.4f}")
        if args.show_probabilities and keys:
            probs = ", ".join(
                f"{key}: {pm_i:.3f}/{po_i:.3f}" for key, pm_i, po_i in zip(keys, pm, po)
            )
            print(f"  probs ({args.monster_label}/{args.control_label}): {probs}")
        print()

    if joint:
        monster_joint = count_joint(monster_rows, joint)
        control_joint = count_joint(control_rows, joint)
        _, pm, po = aligned_probabilities(monster_joint, control_joint)
        js = jensen_shannon(pm, po)
        p_value = permutation_p_value(
            analysis_rows,
            labels,
            lambda subset, joint=joint: count_joint(subset, joint),
            args.group_column,
            args.monster_label,
            args.control_label,
            args.permutations,
            args.seed,
        )
        result["joint"] = {
            "features": joint,
            "monster_counts": dict(monster_joint),
            "control_counts": dict(control_joint),
            "jensen_shannon": js,
            "permutation_p_value": p_value,
        }
        print(f"[joint] {', '.join(joint)}")
        print(f"  {args.monster_label}: {format_counts(monster_joint, args.top_n)}")
        print(f"  {args.control_label}: {format_counts(control_joint, args.top_n)}")
        print(f"  JS={js:.4f} perm_p={p_value:.4f}")
        print()

    for feature in numeric:
        if feature not in rows[0]:
            continue
        monster_summary = numeric_summary(monster_rows, feature)
        control_summary = numeric_summary(control_rows, feature)
        if monster_summary is None and control_summary is None:
            continue
        item = {
            "feature": feature,
            "monster": monster_summary,
            "control": control_summary,
        }
        result["numeric"].append(item)
        print(f"[numeric] {feature}")
        if monster_summary:
            print(
                f"  {args.monster_label}: mean={monster_summary['mean']:.4f} "
                f"std={monster_summary['stddev']:.4f} "
                f"min={monster_summary['min']:.4f} max={monster_summary['max']:.4f}"
            )
        if control_summary:
            print(
                f"  {args.control_label}: mean={control_summary['mean']:.4f} "
                f"std={control_summary['stddev']:.4f} "
                f"min={control_summary['min']:.4f} max={control_summary['max']:.4f}"
            )
        print()

    classifier = naive_bayes_loo_accuracy(analysis_rows, categorical, args.group_column, labels)
    result["loo_naive_bayes"] = classifier
    print("[classification] leave-one-out naive Bayes")
    print(f"  accuracy={classifier['accuracy']:.4f}")

    if args.json:
        print()
        print(json.dumps(result, indent=2, sort_keys=True))

    return 0


def transitions_mode(args: argparse.Namespace) -> int:
    rows = load_rows(Path(args.input))
    require_columns(rows, [args.group_column, args.from_column, args.to_column])
    monster_rows, control_rows = split_groups(
        rows, args.group_column, args.monster_label, args.control_label
    )
    analysis_rows = monster_rows + control_rows
    labels = [row[args.group_column] for row in analysis_rows]

    monster_counts = count_transitions(monster_rows, args.from_column, args.to_column)
    control_counts = count_transitions(control_rows, args.from_column, args.to_column)
    _, pm, po = aligned_probabilities(monster_counts, control_counts)
    js = jensen_shannon(pm, po)
    p_value = permutation_p_value(
        analysis_rows,
        labels,
        lambda subset: count_transitions(subset, args.from_column, args.to_column),
        args.group_column,
        args.monster_label,
        args.control_label,
        args.permutations,
        args.seed,
    )

    print(f"input: {args.input}")
    print(
        f"groups: {args.monster_label}={len(monster_rows)} "
        f"{args.control_label}={len(control_rows)}"
    )
    print(f"transition JS={js:.4f} perm_p={p_value:.4f}")
    print(f"{args.monster_label}: {format_counts(monster_counts, args.top_n)}")
    print(f"{args.control_label}: {format_counts(control_counts, args.top_n)}")

    deltas = []
    all_keys = sorted(set(monster_counts) | set(control_counts))
    total_m = sum(monster_counts.values()) or 1
    total_o = sum(control_counts.values()) or 1
    for key in all_keys:
        pm_i = monster_counts.get(key, 0) / total_m
        po_i = control_counts.get(key, 0) / total_o
        deltas.append((abs(pm_i - po_i), key, pm_i, po_i))
    deltas.sort(reverse=True)

    print()
    print("[largest transition deltas]")
    for _, key, pm_i, po_i in deltas[: args.top_n]:
        print(f"  {key}: {args.monster_label}={pm_i:.3f} {args.control_label}={po_i:.3f}")

    if args.json:
        payload = {
            "input": args.input,
            "mode": "transitions",
            "group_column": args.group_column,
            "monster_label": args.monster_label,
            "control_label": args.control_label,
            "monster_count": len(monster_rows),
            "control_count": len(control_rows),
            "jensen_shannon": js,
            "permutation_p_value": p_value,
            "monster_counts": dict(monster_counts),
            "control_counts": dict(control_counts),
        }
        print()
        print(json.dumps(payload, indent=2, sort_keys=True))
    return 0


def cone_mode(args: argparse.Namespace) -> int:
    rows = inject_default_group(load_rows(Path(args.input)), args.group_column, args.default_group)
    require_columns(rows, [args.group_column, args.name_column, args.time_column, *args.embedding_columns])
    log_columns = set(args.log_columns)
    nonincreasing_columns = set(args.nonincreasing_columns)
    weights = {column: weight for column, weight in zip(args.energy_columns, args.energy_weights)}

    grouped = group_step_rows(rows, args.name_column, args.time_column)
    step_records: List[Dict[str, object]] = []
    for name, trace_rows in grouped.items():
        if len(trace_rows) < 2:
            continue
        embeddings = [
            build_step_embedding(row, args.embedding_columns, log_columns) for row in trace_rows
        ]
        energies = [
            energy_from_embedding(embedding, args.embedding_columns, weights)
            for embedding in embeddings
        ]
        for idx in range(len(trace_rows) - 1):
            start_row = trace_rows[idx]
            end_row = trace_rows[idx + 1]
            delta = vector_subtract(embeddings[idx + 1], embeddings[idx])
            axis_values = {
                column: embeddings[idx][col_idx]
                for col_idx, column in enumerate(args.embedding_columns)
            }
            next_axis_values = {
                column: embeddings[idx + 1][col_idx]
                for col_idx, column in enumerate(args.embedding_columns)
            }
            delta_by_axis = {
                column: delta[col_idx]
                for col_idx, column in enumerate(args.embedding_columns)
            }
            structural_delta = [
                delta[col_idx]
                for col_idx, column in enumerate(args.embedding_columns)
                if column in args.structural_columns
            ]
            structural_signature = ternary_signature(structural_delta, args.struct_eps)
            structural_ultra = ultrametric_signature(structural_delta, args.ultra_thresholds)
            structural_radius = max(structural_ultra) if structural_ultra else 0
            arrow_delta = delta[args.embedding_columns.index(args.arrow_column)]
            hard_failures = []
            for col_idx, column in enumerate(args.embedding_columns):
                if column in nonincreasing_columns and delta[col_idx] > args.tolerance:
                    hard_failures.append(column)
            energy_delta = energies[idx + 1] - energies[idx]
            step_records.append(
                {
                    "name": name,
                    "group": start_row[args.group_column],
                    "t": start_row[args.time_column],
                    "next_t": end_row[args.time_column],
                    "delta": delta,
                    "structural_delta": structural_delta,
                    "structural_signature": structural_signature,
                    "structural_ultra": structural_ultra,
                    "structural_radius": structural_radius,
                    "arrow_delta": arrow_delta,
                    "axis_values": axis_values,
                    "next_axis_values": next_axis_values,
                    "delta_by_axis": delta_by_axis,
                    "delta_norm": vector_norm(delta),
                    "in_cone": not hard_failures,
                    "cone_failures": hard_failures,
                    "energy_delta": energy_delta,
                    "fejer_ok": energy_delta <= args.tolerance,
                }
            )

    if not step_records:
        raise SystemExit("no step deltas produced; need at least two rows per trace")

    present_groups = sorted({str(record["group"]) for record in step_records})
    if args.monster_label not in present_groups:
        raise SystemExit(f"no steps found for group '{args.monster_label}'")
    has_control = args.control_label in present_groups

    training_records = [record for record in step_records if record["group"] == args.monster_label]
    signature_counts: Counter[Tuple[int, ...]] = Counter(
        record["structural_signature"] for record in training_records
    )
    admissible_signatures = {
        signature
        for signature, count in signature_counts.items()
        if count >= args.min_support
    }
    if not admissible_signatures:
        raise SystemExit("no admissible structural signatures survived min-support filtering")

    for record in step_records:
        signature = record["structural_signature"]
        record["structural_ok"] = signature in admissible_signatures
        record["arrow_ok"] = arrow_condition(
            float(record["arrow_delta"]), args.arrow_direction, args.arrow_eps
        )
        record["legacy_joint_ok"] = bool(record["structural_ok"] and record["arrow_ok"])
        record["legacy_status_class"] = classify_step(
            bool(record["structural_ok"]), bool(record["arrow_ok"])
        )
        record["joint_ok"] = record["legacy_joint_ok"]
        record["status_class"] = record["legacy_status_class"]
        record["nearest_signature"] = min(
            admissible_signatures,
            key=lambda candidate: hamming_distance(signature, candidate),
        )
        record["nearest_signature_distance"] = hamming_distance(
            signature, record["nearest_signature"]
        )

    jmd_index: Dict[str, Dict[str, str]] = {}
    if args.jmd_table:
        jmd_index = load_jmd_index(Path(args.jmd_table), args.jmd_key_column)
    if args.emit_dasl_source_json and not args.dasl_source_repo:
        raise SystemExit("--emit-dasl-source-json requires --dasl-source-repo")
    dasl_source_model: Dict[str, object] | None = None
    dasl_distribution: Dict[str, float] = {}
    if args.dasl_source_repo:
        dasl_source_model = load_dasl_source_model(Path(args.dasl_source_repo))
        dasl_distribution = dict(
            dasl_source_model["distributions"].get(args.dasl_distribution, {})  # type: ignore[index]
        )

    trace_records: Dict[str, List[Dict[str, object]]] = defaultdict(list)
    for record in step_records:
        trace_records[str(record["name"])].append(record)

    trace_summaries: List[Dict[str, object]] = []
    legacy_trace_labels: Dict[str, str] = {}
    trace_labels: Dict[str, str] = {}
    jmd_labels: Dict[str, str] = {}
    dasl_labels: Dict[str, str] = {}
    hybrid_labels: Dict[str, str] = {}
    for name in sorted(trace_records):
        subset = trace_records[name]
        legacy_eigenspace_counts: Counter[str] = Counter(
            legacy_signature_to_eigenspace(record["structural_signature"]) for record in subset
        )
        legacy_trace_distribution = normalize_counter(legacy_eigenspace_counts)
        legacy_trace_label, legacy_trace_score = dominant_label(legacy_trace_distribution)

        eigenspace_counts: Counter[str] = Counter(
            refined_signature_to_eigenspace(record["structural_signature"]) for record in subset
        )
        trace_distribution = normalize_counter(eigenspace_counts)
        trace_label, trace_score = dominant_label(trace_distribution)

        jmd_row = jmd_index.get(name, {})
        jmd_label = jmd_row.get(args.jmd_eigen_column, "").strip() or "<missing>"
        jmd_distribution = one_hot_distribution(jmd_label)
        _, jmd_score = dominant_label(jmd_distribution)

        dasl_label, dasl_score = dominant_label(dasl_distribution)
        basin_projection = (
            trace_label
            if trace_distribution.get(trace_label, 0.0) > 0 and dasl_distribution.get(trace_label, 0.0) > 0
            else dasl_label
        )
        basin_support = dasl_distribution.get(trace_label, 0.0)
        basin_js = distribution_js(trace_distribution, dasl_distribution) if dasl_distribution else 0.0
        source_support_ok = basin_support > 0.0 if dasl_distribution else bool(trace_distribution)
        source_support_mode = (
            f"parsed_dasl_{args.dasl_distribution}_catalog" if dasl_distribution else "trace_only_fallback"
        )
        source_projection = (
            canonical_prime_projection(dasl_source_model, args.dasl_distribution, trace_label, dasl_label)
            if dasl_source_model is not None
            else {
                "eigenspace": trace_label,
                "prime": "",
                "hecke": "<missing>",
                "exponent": None,
                "candidate_count": 0,
                "mode": "trace_only_fallback",
            }
        )
        ranked_projection = (
            ranked_prime_projection(
                dasl_source_model,
                args.dasl_distribution,
                trace_distribution,
                trace_label,
                source_projection,
            )
            if dasl_source_model is not None
            else {
                "best": {
                    "eigenspace": trace_label,
                    "prime": "",
                    "hecke": "<missing>",
                    "exponent": None,
                    "score": 0.0,
                    "attack_triple": False,
                    "canonical_alignment": False,
                },
                "top": [],
                "top_role": "diagnostic_shortlist",
                "mode": "trace_only_fallback",
            }
        )
        best_projection = ranked_projection["best"]
        primary_projection = primary_prime_projection(
            args.source_projection_primary,
            source_projection,
            ranked_projection,
        )
        projection_conflict = (
            str(source_projection["eigenspace"]) != str(primary_projection["eigenspace"])
            or str(source_projection["prime"]) != str(primary_projection["prime"])
            or str(source_projection["hecke"]) != str(primary_projection["hecke"])
            or str(source_projection["exponent"]) != str(primary_projection["exponent"])
        )
        projection_conflict_detail = (
            f"canonical={source_projection['eigenspace']}@p{source_projection['prime']}"
            f"/{source_projection['hecke']}/{source_projection['exponent']} "
            f"primary={primary_projection['eigenspace']}@p{primary_projection['prime']}"
            f"/{primary_projection['hecke']}/{primary_projection['exponent']}"
            if projection_conflict
            else "none"
        )
        basin_ok = source_support_ok

        hybrid_distribution = blend_distributions(
            [trace_distribution, jmd_distribution, dasl_distribution]
        )
        hybrid_label, hybrid_score = dominant_label(hybrid_distribution)

        preferred_source = args.eigen_source
        source_distribution_map = {
            "trace": trace_distribution,
            "jmd": jmd_distribution,
            "dasl": dasl_distribution,
            "hybrid": hybrid_distribution,
        }
        selected_source = preferred_source
        selected_distribution = source_distribution_map[selected_source]
        if not selected_distribution:
            for fallback_source in ("trace", "jmd", "dasl", "hybrid"):
                if source_distribution_map[fallback_source]:
                    selected_source = fallback_source
                    selected_distribution = source_distribution_map[fallback_source]
                    break
        selected_label, selected_score = dominant_label(selected_distribution)

        legacy_trace_labels[name] = legacy_trace_label
        trace_labels[name] = trace_label
        if jmd_distribution:
            jmd_labels[name] = jmd_label
        if dasl_distribution:
            dasl_labels[name] = dasl_label
        if hybrid_distribution:
            hybrid_labels[name] = hybrid_label

        for record in subset:
            record["cone_ok"] = bool(record["in_cone"])
            record["mdl_ok"] = bool(record["fejer_ok"])
            record["legacy_trace_eigenspace"] = legacy_trace_label
            record["legacy_trace_eigen_score"] = legacy_trace_score
            record["trace_eigenspace"] = trace_label
            record["trace_eigen_score"] = trace_score
            record["jmd_eigenspace"] = jmd_label
            record["jmd_eigen_score"] = jmd_score
            record["dasl_eigenspace"] = dasl_label
            record["dasl_eigen_score"] = dasl_score
            record["hybrid_eigenspace"] = hybrid_label
            record["hybrid_eigen_score"] = hybrid_score
            record["source_support_projection"] = basin_projection
            record["source_support"] = basin_support
            record["source_support_js"] = basin_js
            record["source_support_ok"] = source_support_ok
            record["source_support_mode"] = source_support_mode
            record["source_projection_eigenspace"] = source_projection["eigenspace"]
            record["source_projection_prime"] = source_projection["prime"]
            record["source_projection_hecke"] = source_projection["hecke"]
            record["source_projection_exponent"] = source_projection["exponent"]
            record["source_projection_candidates"] = source_projection["candidate_count"]
            record["source_projection_mode"] = source_projection["mode"]
            record["source_projection_score"] = best_projection["score"]
            record["source_projection_score_components"] = dict(best_projection.get("score_components", {}))
            record["source_projection_top_role"] = ranked_projection["top_role"]
            record["source_projection_top"] = ranked_projection["top"]
            record["primary_source_projection_mode"] = primary_projection["selection_mode"]
            record["primary_source_projection_eigenspace"] = primary_projection["eigenspace"]
            record["primary_source_projection_prime"] = primary_projection["prime"]
            record["primary_source_projection_hecke"] = primary_projection["hecke"]
            record["primary_source_projection_exponent"] = primary_projection["exponent"]
            record["primary_source_projection_score"] = primary_projection["score"]
            record["primary_source_projection_score_components"] = dict(
                primary_projection.get("score_components", {})
            )
            record["projection_conflict"] = projection_conflict
            record["projection_conflict_detail"] = projection_conflict_detail
            record["basin_projection"] = basin_projection
            record["basin_support"] = basin_support
            record["basin_js"] = basin_js
            record["basin_ok"] = basin_ok
            record["selected_eigen_source"] = selected_source
            record["selected_eigenspace"] = selected_label
            record["selected_eigen_score"] = selected_score
            record["eigen_ok"] = selected_score >= args.eigen_threshold
            record["execution_non_arrow_ok"] = execution_non_arrow_ok(record)
            record["joint_ok"] = bool(record["execution_non_arrow_ok"] and record["arrow_ok"])
            record["status_class"] = classify_step(
                bool(record["execution_non_arrow_ok"]),
                bool(record["arrow_ok"]),
            )

        trace_summaries.append(
            {
                "name": name,
                "group": subset[0]["group"],
                "step_count": len(subset),
                "legacy_trace_eigenspace": legacy_trace_label,
                "legacy_trace_score": f"{legacy_trace_score:.6f}",
                "trace_eigenspace": trace_label,
                "trace_score": f"{trace_score:.6f}",
                "jmd_eigenspace": jmd_label,
                "jmd_score": f"{jmd_score:.6f}",
                "dasl_eigenspace": dasl_label,
                "dasl_score": f"{dasl_score:.6f}",
                "hybrid_eigenspace": hybrid_label,
                "hybrid_score": f"{hybrid_score:.6f}",
                "source_support_projection": basin_projection,
                "source_support": f"{basin_support:.6f}",
                "source_support_js": f"{basin_js:.6f}",
                "source_support_ok": "yes" if source_support_ok else "no",
                "source_support_mode": source_support_mode,
                "source_projection_eigenspace": source_projection["eigenspace"],
                "source_projection_prime": str(source_projection["prime"]),
                "source_projection_hecke": source_projection["hecke"],
                "source_projection_exponent": str(source_projection["exponent"]),
                "source_projection_candidates": str(source_projection["candidate_count"]),
                "source_projection_mode": source_projection["mode"],
                "source_projection_score": f"{float(best_projection['score']):.6f}",
                "source_projection_score_components": format_score_components(
                    dict(best_projection.get("score_components", {}))
                ),
                "source_projection_top_role": ranked_projection["top_role"],
                "source_projection_top": "; ".join(
                    f"{item['eigenspace']}@p{item['prime']}[{item['score']:.4f}|{format_score_components(dict(item.get('score_components', {})))}]"
                    for item in ranked_projection["top"]
                ),
                "primary_source_projection_mode": primary_projection["selection_mode"],
                "primary_source_projection_eigenspace": primary_projection["eigenspace"],
                "primary_source_projection_prime": str(primary_projection["prime"]),
                "primary_source_projection_hecke": primary_projection["hecke"],
                "primary_source_projection_exponent": str(primary_projection["exponent"]),
                "primary_source_projection_score": f"{float(primary_projection['score']):.6f}",
                "primary_source_projection_score_components": format_score_components(
                    dict(primary_projection.get("score_components", {}))
                ),
                "projection_conflict": "yes" if projection_conflict else "no",
                "projection_conflict_detail": projection_conflict_detail,
                "basin_projection": basin_projection,
                "basin_support": f"{basin_support:.6f}",
                "basin_js": f"{basin_js:.6f}",
                "basin_ok": "yes" if basin_ok else "no",
                "selected_source": selected_source,
                "selected_eigenspace": selected_label,
                "selected_score": f"{selected_score:.6f}",
                "jmd_coverage": "yes" if jmd_distribution else "no",
                "dasl_coverage": "yes" if dasl_distribution else "no",
            }
        )

    def summarize(group_label: str) -> Dict[str, object]:
        subset = [record for record in step_records if record["group"] == group_label]
        total = len(subset)
        cone_passes = sum(1 for record in subset if record["in_cone"])
        fejer_passes = sum(1 for record in subset if record["fejer_ok"])
        structural_passes = sum(1 for record in subset if record["structural_ok"])
        arrow_passes = sum(1 for record in subset if record["arrow_ok"])
        joint_passes = sum(1 for record in subset if record["joint_ok"])
        violation_counts: Counter[str] = Counter()
        radius_counts: Counter[int] = Counter()
        ultra_counts: Counter[str] = Counter()
        status_counts: Counter[str] = Counter()
        for record in subset:
            for column in record["cone_failures"]:
                violation_counts[column] += 1
            radius_counts[int(record["structural_radius"])] += 1
            ultra_counts[",".join(str(item) for item in record["structural_ultra"])] += 1
            status_counts[str(record["status_class"])] += 1
        structural_counts: Counter[str] = Counter(
            ",".join(str(item) for item in record["structural_signature"]) for record in subset
        )
        return {
            "total_steps": total,
            "cone_pass_rate": cone_passes / total if total else 0.0,
            "fejer_pass_rate": fejer_passes / total if total else 0.0,
            "structural_cone_pass_rate": structural_passes / total if total else 0.0,
            "arrow_pass_rate": arrow_passes / total if total else 0.0,
            "joint_pass_rate": joint_passes / total if total else 0.0,
            "mean_delta_norm": mean([record["delta_norm"] for record in subset]),
            "mean_energy_delta": mean([record["energy_delta"] for record in subset]),
            "mean_arrow_delta": mean([float(record["arrow_delta"]) for record in subset]),
            "violations": dict(violation_counts),
            "top_structural_signatures": dict(structural_counts.most_common(args.top_n)),
            "top_ultrametric_signatures": dict(ultra_counts.most_common(args.top_n)),
            "radius_histogram": dict(sorted(radius_counts.items())),
            "status_counts": dict(status_counts),
        }

    monster_summary = summarize(args.monster_label)
    control_summary = summarize(args.control_label) if has_control else None
    cone_js = None
    if has_control:
        monster_transitions = [
            {
                args.group_column: args.monster_label,
                "status": "pass" if record["in_cone"] else "fail",
            }
            for record in step_records
            if record["group"] == args.monster_label
        ]
        control_transitions = [
            {
                args.group_column: args.control_label,
                "status": "pass" if record["in_cone"] else "fail",
            }
            for record in step_records
            if record["group"] == args.control_label
        ]
        cone_counts_m = count_values(monster_transitions, "status")
        cone_counts_o = count_values(control_transitions, "status")
        _, pm, po = aligned_probabilities(cone_counts_m, cone_counts_o)
        cone_js = jensen_shannon(pm, po)

    legacy_trace_agreements, legacy_trace_shared, legacy_trace_rate = agreement_rate(
        legacy_trace_labels, trace_labels
    )
    trace_jmd_agreements, trace_jmd_shared, trace_jmd_rate = agreement_rate(trace_labels, jmd_labels)
    trace_dasl_agreements, trace_dasl_shared, trace_dasl_rate = agreement_rate(trace_labels, dasl_labels)
    trace_hybrid_agreements, trace_hybrid_shared, trace_hybrid_rate = agreement_rate(trace_labels, hybrid_labels)
    jmd_hybrid_agreements, jmd_hybrid_shared, jmd_hybrid_rate = agreement_rate(jmd_labels, hybrid_labels)

    print(f"input: {args.input}")
    if has_control and control_summary is not None:
        print(
            f"groups: {args.monster_label}={monster_summary['total_steps']} steps "
            f"{args.control_label}={control_summary['total_steps']} steps"
        )
    else:
        print(f"group: {args.monster_label}={monster_summary['total_steps']} steps")
    print(f"embedding: {', '.join(args.embedding_columns)}")
    print(f"structural axes: {', '.join(args.structural_columns)}")
    print(f"arrow axis: {args.arrow_column}")
    print(f"hard cone columns: {', '.join(args.nonincreasing_columns)}")
    print(
        f"learned structural signatures (eps={args.struct_eps:.4f}, min_support={args.min_support}): "
        + ", ".join(str(signature) for signature in sorted(admissible_signatures))
    )
    print(
        "ultrametric thresholds: "
        + ", ".join(f"{threshold:g}" for threshold in args.ultra_thresholds)
    )
    if args.arrow_direction == "nondecreasing":
        print(f"arrow guard: delta({args.arrow_column}) >= {-args.arrow_eps:.4f}")
    else:
        print(f"arrow guard: delta({args.arrow_column}) <= {args.arrow_eps:.4f}")
    if args.arrow_profile:
        print(f"arrow profile: {args.arrow_profile}")
    print(
        f"energy: "
        + ", ".join(f"{column}={weights[column]:.3f}" for column in args.energy_columns)
    )
    print()
    print(f"[{args.monster_label}]")
    print(
        f"  cone_pass_rate={monster_summary['cone_pass_rate']:.4f} "
        f"fejer_pass_rate={monster_summary['fejer_pass_rate']:.4f}"
    )
    print(
        f"  structural_cone_pass_rate={monster_summary['structural_cone_pass_rate']:.4f} "
        f"arrow_pass_rate={monster_summary['arrow_pass_rate']:.4f} "
        f"joint_pass_rate={monster_summary['joint_pass_rate']:.4f}"
    )
    print(
        f"  mean_delta_norm={monster_summary['mean_delta_norm']:.4f} "
        f"mean_energy_delta={monster_summary['mean_energy_delta']:.4f} "
        f"mean_arrow_delta={monster_summary['mean_arrow_delta']:.4f}"
    )
    print(f"  violations={monster_summary['violations']}")
    print(f"  top_structural_signatures={monster_summary['top_structural_signatures']}")
    print(f"  top_ultrametric_signatures={monster_summary['top_ultrametric_signatures']}")
    print(f"  radius_histogram={monster_summary['radius_histogram']}")
    print(f"  status_counts={monster_summary['status_counts']}")
    print()
    if has_control and control_summary is not None:
        print(f"[{args.control_label}]")
        print(
            f"  cone_pass_rate={control_summary['cone_pass_rate']:.4f} "
            f"fejer_pass_rate={control_summary['fejer_pass_rate']:.4f}"
        )
        print(
            f"  structural_cone_pass_rate={control_summary['structural_cone_pass_rate']:.4f} "
            f"arrow_pass_rate={control_summary['arrow_pass_rate']:.4f} "
            f"joint_pass_rate={control_summary['joint_pass_rate']:.4f}"
        )
        print(
            f"  mean_delta_norm={control_summary['mean_delta_norm']:.4f} "
            f"mean_energy_delta={control_summary['mean_energy_delta']:.4f} "
            f"mean_arrow_delta={control_summary['mean_arrow_delta']:.4f}"
        )
        print(f"  violations={control_summary['violations']}")
        print(f"  top_structural_signatures={control_summary['top_structural_signatures']}")
        print(f"  top_ultrametric_signatures={control_summary['top_ultrametric_signatures']}")
        print(f"  radius_histogram={control_summary['radius_histogram']}")
        print(f"  status_counts={control_summary['status_counts']}")
        print()
        print(f"cone status JS={cone_js:.4f}")

    violations = [record for record in step_records if not record["in_cone"]]
    violations.sort(key=lambda record: record["delta_norm"], reverse=True)
    print()
    print("[largest cone violations]")
    for record in violations[: args.top_n]:
        print(
            f"  {record['name']} t={record['t']}->{record['next_t']} "
            f"group={record['group']} fail={','.join(record['cone_failures'])} "
            f"class={record['status_class']} "
            f"struct_ok={record['structural_ok']} arrow_ok={record['arrow_ok']} "
            f"sig={record['structural_signature']} "
            f"ultra={record['structural_ultra']} radius={record['structural_radius']} "
            f"nearest={record['nearest_signature']} "
            f"hamming={record['nearest_signature_distance']} "
            f"energy_delta={record['energy_delta']:.4f} "
            f"delta_norm={record['delta_norm']:.4f}"
        )

    boundary_records = [record for record in step_records if not record["joint_ok"]]
    boundary_records.sort(
        key=lambda record: (record["nearest_signature_distance"], record["structural_radius"], record["delta_norm"]),
        reverse=True,
    )
    family_contexts: Dict[str, Dict[str, object]] = {}
    dashifine_context_root = infer_dashifine_context_root(Path(args.input))
    if dashifine_context_root is not None:
        for family_name in sorted(trace_records):
            family_context = load_dashifine_family_context(Path(args.input), family_name)
            if family_context is not None:
                family_contexts[family_name] = family_context
    arrow_boundary_family_summaries = summarize_arrow_boundary_families(
        step_records,
        family_contexts if family_contexts else None,
    )
    family_classification_records = build_family_classification_records(
        trace_records,
        arrow_boundary_family_summaries,
        family_contexts,
    )
    tail_boundary_lemma_summary = summarize_tail_boundary_lemma(
        family_classification_records
    )
    print()
    print("[ultrametric/ternary boundary report]")
    for record in boundary_records[: args.top_n]:
        print(
            f"  {record['name']} t={record['t']}->{record['next_t']} "
            f"group={record['group']} class={record['status_class']} "
            f"sig={record['structural_signature']} "
            f"ultra={record['structural_ultra']} radius={record['structural_radius']} "
            f"nearest={record['nearest_signature']} "
            f"hamming={record['nearest_signature_distance']} "
            f"arrow_delta={record['arrow_delta']:.4f} "
            f"joint_ok={record['joint_ok']}"
        )
    if arrow_boundary_family_summaries:
        print()
        print("[arrow boundary families]")
        for summary in arrow_boundary_family_summaries[: args.top_n]:
            print(
                f"  {summary['name']} count={summary['count']} "
                f"class={summary['family_class']} "
                f"base={summary['family_class_base']} "
                f"min_eps={summary['min_required_eps']:.6g} "
                f"max_eps={summary['max_required_eps']:.6g} "
                f"mean_eps={summary['mean_required_eps']:.6g} "
                f"failure_axes={summary['failure_axes']} "
                f"profiles={summary['profile_clearance']} "
                f"top_signatures={summary['top_structural_signatures']}"
            )
    print()
    print("[tail boundary lemma]")
    print(
        f"  families={tail_boundary_lemma_summary['family_count']} "
        f"mdl_tail_boundary={tail_boundary_lemma_summary['mdl_tail_boundary_count']} "
        f"tail_localized={tail_boundary_lemma_summary['mdl_tail_boundary_all_tail_localized']} "
        f"terminal_boundary={tail_boundary_lemma_summary['mdl_tail_boundary_all_terminal_boundary']}"
    )
    print(
        f"  cone_ok={tail_boundary_lemma_summary['mdl_tail_boundary_all_cone_ok']} "
        f"fejer_ok={tail_boundary_lemma_summary['mdl_tail_boundary_all_fejer_ok']} "
        f"closest_ok={tail_boundary_lemma_summary['mdl_tail_boundary_all_closest_ok']} "
        f"mdl_exact_fail={tail_boundary_lemma_summary['mdl_tail_boundary_all_mdl_exact_fail']}"
    )
    print(
        f"  families={tail_boundary_lemma_summary['mdl_tail_boundary_families']} "
        f"class_counts={tail_boundary_lemma_summary['class_counts']}"
    )
    family_drilldown = None
    if args.focus_family:
        family_context = load_dashifine_family_context(Path(args.input), args.focus_family)
        family_drilldown = build_family_drilldown(step_records, args.focus_family, family_context)
        print()
        print("[focused family]")
        print(
            f"  {family_drilldown['name']} step_count={family_drilldown['step_count']} "
            f"boundary_count={family_drilldown['boundary_count']}"
        )
        family_context = family_drilldown.get("family_context")
        if isinstance(family_context, dict):
            tail_summary = family_context.get("tail_summary")
            if isinstance(tail_summary, dict):
                print(
                    f"  tail bins={tail_summary['bin_count']} "
                    f"last_bin_x={tail_summary['last_bin_x']:.6g} "
                    f"last_bin_frac_err={tail_summary['last_bin_frac_err']:.6g} "
                    f"tail_max_frac_err={tail_summary['tail_has_max_fractional_uncertainty']}"
                )
            report_summary = family_context.get("report_summary")
            if isinstance(report_summary, dict):
                closest_rows = report_summary.get("closestpoint")
                fejer_rows = report_summary.get("fejer_set")
                mdl_rows = report_summary.get("mdl_descent")
                defect_rows = report_summary.get("defect_monotonicity")
                if isinstance(closest_rows, list) and closest_rows:
                    closest = closest_rows[0]
                    print(
                        f"  closestpoint {closest['metric']} frac={closest['closest_frac']:.6g} "
                        f"max_violation={closest['closest_max_violation']:.6g}"
                    )
                if isinstance(fejer_rows, list) and fejer_rows:
                    fejer = fejer_rows[0]
                    print(
                        f"  fejer_set {fejer['metric']} frac={fejer['fejer_set_frac']:.6g} "
                        f"max_violation={fejer['fejer_set_max_violation']:.6g}"
                    )
                if isinstance(mdl_rows, list) and mdl_rows:
                    mdl = mdl_rows[0]
                    print(
                        f"  mdl_exact monotone={mdl['MDL_monotone']} "
                        f"violations={mdl['MDL_violations']} "
                        f"worst_iter={mdl['MDL_worst_iter']} "
                        f"worst_increase={mdl['MDL_worst_increase']:.6g}"
                    )
                if isinstance(defect_rows, list) and defect_rows:
                    defect = defect_rows[0]
                    print(
                        f"  defect L1={defect['L1_monotone']} "
                        f"L2={defect['L2_monotone']} "
                        f"L2_worst_increase={defect['L2_worst_increase']:.6g}"
                    )
        boundary_summary = family_drilldown["boundary_summary"]
        if boundary_summary:
            summary = boundary_summary[0]
            print(
                f"  class={summary['family_class']} min_eps={summary['min_required_eps']:.6g} "
                f"max_eps={summary['max_required_eps']:.6g} mean_eps={summary['mean_required_eps']:.6g} "
                f"failure_axes={summary['failure_axes']} profiles={summary['profile_clearance']}"
            )
            print(
                f"  class_base={summary['family_class_base']} "
                f"class_reason={summary['family_class_reason']}"
            )
        onset = family_drilldown["onset"]
        if onset is not None:
            print(
                f"  onset index={onset['first_boundary_index']} "
                f"t={onset['first_boundary_t']}->{onset['first_boundary_next_t']} "
                f"mode={onset['failure_mode']} sign_flip={onset['arrow_sign_flip']} "
                f"sig_changed={onset['signature_changed']} "
                f"failures={onset['first_boundary_failures']}"
            )
            metrics = family_context.get("metrics") if isinstance(family_context, dict) else None
            if isinstance(metrics, list):
                try:
                    onset_idx = int(onset["first_boundary_index"])
                    if 0 <= onset_idx < len(metrics) - 1:
                        start_metrics = metrics[onset_idx]
                        end_metrics = metrics[onset_idx + 1]
                        print(
                            f"  onset alpha={start_metrics['alpha']:.6g}->{end_metrics['alpha']:.6g} "
                            f"chi2_dof={start_metrics['chi2_dof']:.6g}->{end_metrics['chi2_dof']:.6g} "
                            f"R_E_hi={start_metrics['R_E_hi']:.6g}->{end_metrics['R_E_hi']:.6g}"
                        )
                except (KeyError, TypeError, ValueError):
                    pass
        alt_v_dnorm = family_drilldown.get("alt_v_dnorm")
        if isinstance(alt_v_dnorm, dict):
            print("  alt_v_dnorm:")
            for kind, payload in alt_v_dnorm.items():
                boundary_failures = payload.get("boundary_failures", [])
                deltas = ", ".join(
                    f"{item['t']}->{item['next_t']}:{item['delta']:.6g}:{'ok' if item['nonincreasing_ok'] else 'fail'}"
                    for item in boundary_failures
                ) or "<none>"
                print(f"    {kind}: {deltas}")
        for record in family_drilldown["records"][: args.top_n]:
            print(
                f"  t={record['t']}->{record['next_t']} class={record['status_class']} "
                f"fail={','.join(record['cone_failures']) or '<none>'} "
                f"sig={tuple(record['structural_signature'])} ultra={tuple(record['structural_ultra'])} "
                f"arrow_delta={record['arrow_delta']:.6g} energy_delta={record['energy_delta']:.6g}"
            )

    print()
    print("[eigen overlap]")
    print(
        f"  preferred_source={args.eigen_source} selected_threshold={args.eigen_threshold:.3f} "
        f"trace_coverage={len(trace_labels)} jmd_coverage={len(jmd_labels)} "
        f"dasl_coverage={len(dasl_labels)} hybrid_coverage={len(hybrid_labels)}"
    )
    if dasl_source_model is not None:
        print(
            f"  dasl_distribution={args.dasl_distribution} "
            f"catalog_count={dasl_source_model['counts'].get(args.dasl_distribution, 0)}"
        )
    print(
        f"  legacy_vs_refined_trace_agreement={legacy_trace_agreements}/{legacy_trace_shared} ({legacy_trace_rate:.4f})"
    )
    print(
        f"  trace_vs_jmd_agreement={trace_jmd_agreements}/{trace_jmd_shared} ({trace_jmd_rate:.4f})"
    )
    print(
        f"  trace_vs_dasl_agreement={trace_dasl_agreements}/{trace_dasl_shared} ({trace_dasl_rate:.4f})"
    )
    print(
        f"  trace_vs_hybrid_agreement={trace_hybrid_agreements}/{trace_hybrid_shared} ({trace_hybrid_rate:.4f})"
    )
    print(
        f"  jmd_vs_hybrid_agreement={jmd_hybrid_agreements}/{jmd_hybrid_shared} ({jmd_hybrid_rate:.4f})"
    )
    for row in trace_summaries[: args.top_n]:
        print(
            f"  {row['name']} group={row['group']} "
            f"legacy_trace={row['legacy_trace_eigenspace']}({row['legacy_trace_score']}) "
            f"trace={row['trace_eigenspace']}({row['trace_score']}) "
            f"jmd={row['jmd_eigenspace']}({row['jmd_score']}) "
            f"dasl={row['dasl_eigenspace']}({row['dasl_score']}) "
            f"hybrid={row['hybrid_eigenspace']}({row['hybrid_score']}) "
            f"source_support={row['source_support_projection']} support={row['source_support']} js={row['source_support_js']} ok={row['source_support_ok']} "
            f"mode={row['source_support_mode']} "
            f"source_projection={row['source_projection_eigenspace']}@p{row['source_projection_prime']} "
            f"hecke={row['source_projection_hecke']} exp={row['source_projection_exponent']} "
            f"candidates={row['source_projection_candidates']} proj_mode={row['source_projection_mode']} "
            f"score={row['source_projection_score']} components={row['source_projection_score_components']} "
            f"top_role={row['source_projection_top_role']} top={row['source_projection_top']} "
            f"primary_projection={row['primary_source_projection_mode']}:{row['primary_source_projection_eigenspace']}@p{row['primary_source_projection_prime']} "
            f"hecke={row['primary_source_projection_hecke']} exp={row['primary_source_projection_exponent']} "
            f"score={row['primary_source_projection_score']} components={row['primary_source_projection_score_components']} "
            f"projection_conflict={row['projection_conflict']} detail={row['projection_conflict_detail']} "
            f"basin_ok={row['basin_ok']} "
            f"selected={row['selected_source']}:{row['selected_eigenspace']}({row['selected_score']})"
        )

    sweep_values = args.arrow_sweep
    if sweep_values:
        print()
        print("[arrow guard sweep]")
        for eps in sweep_values:
            arrow_passes = sum(
                1
                for record in step_records
                if arrow_condition(float(record["arrow_delta"]), args.arrow_direction, eps)
            )
            joint_passes = sum(
                1
                for record in step_records
                if record["structural_ok"]
                and arrow_condition(float(record["arrow_delta"]), args.arrow_direction, eps)
            )
            print(
                f"  eps={eps:.6g} "
                f"arrow_pass_rate={arrow_passes / len(step_records):.4f} "
                f"joint_pass_rate={joint_passes / len(step_records):.4f}"
            )

        target_records = boundary_records if boundary_records else step_records
        print()
        print("[minimum arrow eps per current boundary step]")
        for record in target_records[: args.top_n]:
            required_eps = abs(float(record["arrow_delta"]))
            print(
                f"  {record['name']} t={record['t']}->{record['next_t']} "
                f"arrow_delta={record['arrow_delta']:.6g} "
                f"min_eps={required_eps:.6g}"
            )

    export_target = args.boundary_csv
    if args.write_default_boundary_artifact:
        export_target = str(ROOT_DIR / "artifacts" / "regime_test" / "arrow_boundary_latest.csv")
    if export_target:
        export_path = Path(export_target)
        export_path.parent.mkdir(parents=True, exist_ok=True)
        with export_path.open("w", encoding="utf-8", newline="") as fh:
            writer = csv.writer(fh)
            writer.writerow(
                [
                    "name",
                    "group",
                    "t",
                    "next_t",
                    "status_class",
                    "structural_signature",
                    "structural_ultra",
                    "structural_radius",
                    "nearest_signature",
                    "nearest_signature_distance",
                    "arrow_delta",
                    "energy_delta",
                    "delta_norm",
                ]
            )
            for record in boundary_records:
                writer.writerow(
                    [
                        record["name"],
                        record["group"],
                        record["t"],
                        record["next_t"],
                        record["status_class"],
                        ",".join(str(item) for item in record["structural_signature"]),
                        ",".join(str(item) for item in record["structural_ultra"]),
                        record["structural_radius"],
                        ",".join(str(item) for item in record["nearest_signature"]),
                        record["nearest_signature_distance"],
                        f"{float(record['arrow_delta']):.12g}",
                        f"{float(record['energy_delta']):.12g}",
                        f"{float(record['delta_norm']):.12g}",
                    ]
                )
        print()
        print(f"[boundary export] wrote {len(boundary_records)} rows to {export_path}")
        if args.write_default_boundary_artifact:
            family_export_path = ROOT_DIR / "artifacts" / "regime_test" / "arrow_boundary_family_latest.json"
            emit_json(family_export_path, arrow_boundary_family_summaries)
            print(f"[boundary family export] wrote {len(arrow_boundary_family_summaries)} families to {family_export_path}")
    if args.emit_family_json and family_drilldown is not None:
        family_json_path = Path(args.emit_family_json)
        emit_json(family_json_path, family_drilldown)
        print(f"[family json] wrote focused family to {family_json_path}")

    if args.emit_eigen_csv:
        eigen_path = Path(args.emit_eigen_csv)
        emit_eigen_csv(eigen_path, trace_summaries)
        print(f"[eigen csv] wrote {len(trace_summaries)} rows to {eigen_path}")
    if args.emit_dasl_source_json and dasl_source_model is not None:
        dasl_source_json_path = Path(args.emit_dasl_source_json)
        emit_dasl_source_json(dasl_source_json_path, dasl_source_model)
        print(f"[dasl source json] wrote source model to {dasl_source_json_path}")

    execution_payload = {
        "input": args.input,
        "mode": "cone",
        "embedding_columns": args.embedding_columns,
        "structural_columns": args.structural_columns,
        "arrow_column": args.arrow_column,
        "struct_eps": args.struct_eps,
        "arrow_eps": args.arrow_eps,
        "arrow_profile": args.arrow_profile,
        "monster_label": args.monster_label,
        "control_label": args.control_label,
        "eigen_source": args.eigen_source,
        "eigen_threshold": args.eigen_threshold,
        "dasl_source_repo": str(args.dasl_source_repo) if args.dasl_source_repo else None,
        "dasl_distribution": args.dasl_distribution,
        "basin_mode": "source_support_proxy",
        "basin_ok_alias_for": "source_support_ok",
        "source_projection_mode": "canonical_by_eigenspace_exponent",
        "primary_source_projection_mode": args.source_projection_primary,
        "projection_conflict_semantics": "canonical_vs_primary_source_projection_divergence",
        "source_projection_top_role": "diagnostic_shortlist",
        "arrow_boundary_families": arrow_boundary_family_summaries,
        "family_classification": family_classification_records,
        "tail_boundary_lemma_summary": tail_boundary_lemma_summary,
        "focused_family": family_drilldown,
        "monster_summary": monster_summary,
        "control_summary": control_summary,
        "dasl_source_model": dasl_source_model,
        "trace_summaries": trace_summaries,
        "step_records": [
            {
                "name": record["name"],
                "group": record["group"],
                "t": record["t"],
                "next_t": record["next_t"],
                "status_class": record["status_class"],
                "structural_signature": list(record["structural_signature"]),
                "structural_ultra": list(record["structural_ultra"]),
                "structural_radius": record["structural_radius"],
                "nearest_signature": list(record["nearest_signature"]),
                "nearest_signature_distance": record["nearest_signature_distance"],
                "arrow_delta": float(record["arrow_delta"]),
                "energy_delta": float(record["energy_delta"]),
                "delta_norm": float(record["delta_norm"]),
                "cone_failures": list(record["cone_failures"]),
                "structural_ok": bool(record["structural_ok"]),
                "cone_ok": bool(record.get("cone_ok", record["in_cone"])),
                "mdl_ok": bool(record.get("mdl_ok", record["fejer_ok"])),
                "arrow_ok": bool(record["arrow_ok"]),
                "execution_non_arrow_ok": bool(record.get("execution_non_arrow_ok", False)),
                "joint_ok": bool(record["joint_ok"]),
                "legacy_joint_ok": bool(record.get("legacy_joint_ok", False)),
                "legacy_status_class": str(record.get("legacy_status_class", record["status_class"])),
                "fejer_ok": bool(record["fejer_ok"]),
                "legacy_trace_eigenspace": record["legacy_trace_eigenspace"],
                "legacy_trace_eigen_score": float(record["legacy_trace_eigen_score"]),
                "basin_projection": record["basin_projection"],
                "basin_support": float(record["basin_support"]),
                "basin_js": float(record["basin_js"]),
                "source_support_projection": record["source_support_projection"],
                "source_support": float(record["source_support"]),
                "source_support_js": float(record["source_support_js"]),
                "source_support_ok": bool(record["source_support_ok"]),
                "source_support_mode": record["source_support_mode"],
                "source_projection_eigenspace": record["source_projection_eigenspace"],
                "source_projection_prime": record["source_projection_prime"],
                "source_projection_hecke": record["source_projection_hecke"],
                "source_projection_exponent": record["source_projection_exponent"],
                "source_projection_candidates": record["source_projection_candidates"],
                "source_projection_mode": record["source_projection_mode"],
                "source_projection_score": float(record["source_projection_score"]),
                "source_projection_score_components": dict(record["source_projection_score_components"]),
                "source_projection_top_role": record["source_projection_top_role"],
                "source_projection_top": list(record["source_projection_top"]),
                "primary_source_projection_mode": record["primary_source_projection_mode"],
                "primary_source_projection_eigenspace": record["primary_source_projection_eigenspace"],
                "primary_source_projection_prime": record["primary_source_projection_prime"],
                "primary_source_projection_hecke": record["primary_source_projection_hecke"],
                "primary_source_projection_exponent": record["primary_source_projection_exponent"],
                "primary_source_projection_score": float(record["primary_source_projection_score"]),
                "primary_source_projection_score_components": dict(
                    record["primary_source_projection_score_components"]
                ),
                "projection_conflict": bool(record["projection_conflict"]),
                "projection_conflict_detail": record["projection_conflict_detail"],
                "basin_ok": bool(record["basin_ok"]),
                "dasl_eigenspace": record["dasl_eigenspace"],
                "dasl_eigen_score": float(record["dasl_eigen_score"]),
                "selected_eigen_source": record["selected_eigen_source"],
                "selected_eigenspace": record["selected_eigenspace"],
                "selected_eigen_score": float(record["selected_eigen_score"]),
                "eigen_ok": bool(record["eigen_ok"]),
            }
            for record in sorted(step_records, key=lambda item: (str(item["name"]), float(str(item["t"]))))
        ],
    }

    if args.emit_execution_json:
        execution_json_path = Path(args.emit_execution_json)
        emit_execution_json(execution_json_path, execution_payload)
        print(f"[execution json] wrote {len(execution_payload['step_records'])} rows to {execution_json_path}")

    if args.emit_family_witness_json:
        family_json_path = Path(args.emit_family_witness_json)
        emit_family_classification_json(family_json_path, family_classification_records)
        print(f"[family witness json] wrote {len(family_classification_records)} rows to {family_json_path}")
    if args.emit_tail_boundary_summary_json:
        tail_boundary_summary_path = Path(args.emit_tail_boundary_summary_json)
        emit_tail_boundary_summary_json(tail_boundary_summary_path, tail_boundary_lemma_summary)
        print(f"[tail boundary summary] wrote summary to {tail_boundary_summary_path}")

    if args.emit_agda_witness:
        agda_path = Path(args.emit_agda_witness)
        module_name = args.agda_module_name or agda_module_name_from_path(agda_path)
        emit_agda_witness(agda_path, module_name, execution_payload["step_records"])
        print(f"[agda witness] wrote {len(execution_payload['step_records'])} rows to {agda_path}")
    if args.emit_agda_family_witness:
        agda_family_path = Path(args.emit_agda_family_witness)
        family_module_name = args.agda_family_module_name or agda_module_name_from_path(agda_family_path)
        emit_agda_family_witness(agda_family_path, family_module_name, family_classification_records)
        print(f"[agda family witness] wrote {len(family_classification_records)} rows to {agda_family_path}")

    if args.json:
        print()
        print(json.dumps(execution_payload, indent=2, sort_keys=True))
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="CSV-driven JMD regime and DASHI transition analysis harness"
    )
    subparsers = parser.add_subparsers(dest="mode", required=True)

    occupancy = subparsers.add_parser(
        "occupancy",
        help="compare regime occupancy/divergence between two labeled groups",
    )
    occupancy.add_argument("input", help="CSV file with one row per module/sample")
    occupancy.add_argument("--group-column", default="group")
    occupancy.add_argument("--monster-label", default="M")
    occupancy.add_argument("--control-label", default="O")
    occupancy.add_argument("--categorical", default=",".join(DEFAULT_CATEGORICAL))
    occupancy.add_argument("--joint", default=",".join(DEFAULT_JOINT))
    occupancy.add_argument("--numeric", default=",".join(DEFAULT_NUMERIC))
    occupancy.add_argument("--permutations", type=int, default=2000)
    occupancy.add_argument("--seed", type=int, default=12345)
    occupancy.add_argument("--top-n", type=int, default=8)
    occupancy.add_argument("--show-probabilities", action="store_true")
    occupancy.add_argument("--json", action="store_true")
    occupancy.set_defaults(func=occupancy_mode)

    transitions = subparsers.add_parser(
        "transitions",
        help="compare transition distributions between two labeled groups",
    )
    transitions.add_argument("input", help="CSV file with one row per transition")
    transitions.add_argument("--group-column", default="group")
    transitions.add_argument("--monster-label", default="M")
    transitions.add_argument("--control-label", default="O")
    transitions.add_argument("--from-column", default="regime_from")
    transitions.add_argument("--to-column", default="regime_to")
    transitions.add_argument("--permutations", type=int, default=2000)
    transitions.add_argument("--seed", type=int, default=12345)
    transitions.add_argument("--top-n", type=int, default=10)
    transitions.add_argument("--json", action="store_true")
    transitions.set_defaults(func=transitions_mode)

    cone = subparsers.add_parser(
        "cone",
        help="compare DASHI-style step deltas, hard cone checks, and Fejer-style energy drift",
    )
    cone.add_argument("input", help="CSV file with one row per trace step")
    cone.add_argument("--group-column", default="group")
    cone.add_argument("--monster-label", default="M")
    cone.add_argument("--control-label", default="O")
    cone.add_argument(
        "--default-group",
        default=None,
        help="inject this group label when the input file has no group column",
    )
    cone.add_argument("--name-column", default="name")
    cone.add_argument("--time-column", default="t")
    cone.add_argument(
        "--preset",
        choices=["dashifine-closure-embedding"],
        default=None,
        help="apply a known input schema preset before other cone arguments",
    )
    cone.add_argument(
        "--embedding-columns",
        default="mass,cycles,instr,depth,reach,p59,p71,trivector_sum",
        type=lambda raw: parse_csv_list(raw, []),
    )
    cone.add_argument(
        "--structural-columns",
        default="mass,cycles,instr,depth,reach,p59,p71,trivector_sum",
        type=lambda raw: parse_csv_list(raw, []),
    )
    cone.add_argument("--arrow-column", default="reach")
    cone.add_argument(
        "--log-columns",
        default="cycles,instr",
        type=lambda raw: parse_csv_list(raw, []),
    )
    cone.add_argument(
        "--nonincreasing-columns",
        default="mass,cycles,instr",
        type=lambda raw: parse_csv_list(raw, []),
    )
    cone.add_argument(
        "--energy-columns",
        default="cycles,instr,mass",
        type=lambda raw: parse_csv_list(raw, []),
    )
    cone.add_argument(
        "--energy-weights",
        default="1.0,1.0,0.1",
        type=lambda raw: [float(item) for item in parse_csv_list(raw, [])],
    )
    cone.add_argument("--struct-eps", type=float, default=1e-9)
    cone.add_argument("--arrow-eps", type=float, default=0.0)
    cone.add_argument(
        "--arrow-profile",
        choices=sorted(ARROW_PROFILES),
        default=None,
        help="named arrow guard profile; overrides --arrow-eps",
    )
    cone.add_argument(
        "--arrow-sweep",
        default="0,1e-6,1e-4,1e-3,1e-2,1e-1",
        type=lambda raw: [float(item) for item in parse_csv_list(raw, [])],
    )
    cone.add_argument(
        "--ultra-thresholds",
        default="1e-9,1e-6,1e-3,1e-1,1",
        type=lambda raw: [float(item) for item in parse_csv_list(raw, [])],
    )
    cone.add_argument(
        "--arrow-direction",
        choices=["nondecreasing", "nonincreasing"],
        default="nondecreasing",
    )
    cone.add_argument("--min-support", type=int, default=1)
    cone.add_argument("--tolerance", type=float, default=0.0)
    cone.add_argument("--top-n", type=int, default=10)
    cone.add_argument("--focus-family", default=None)
    cone.add_argument("--emit-family-json", default=None)
    cone.add_argument("--boundary-csv", default=None)
    cone.add_argument("--write-default-boundary-artifact", action="store_true")
    cone.add_argument("--emit-execution-json", default=None)
    cone.add_argument("--emit-family-witness-json", default=None)
    cone.add_argument("--emit-tail-boundary-summary-json", default=None)
    cone.add_argument("--emit-eigen-csv", default=None)
    cone.add_argument("--emit-dasl-source-json", default=None)
    cone.add_argument("--emit-agda-witness", default=None)
    cone.add_argument("--agda-module-name", default=None)
    cone.add_argument("--emit-agda-family-witness", default=None)
    cone.add_argument("--agda-family-module-name", default=None)
    cone.add_argument("--jmd-table", default=None)
    cone.add_argument("--jmd-key-column", default="name")
    cone.add_argument("--jmd-eigen-column", default="eigenspace")
    cone.add_argument("--dasl-source-repo", default=None)
    cone.add_argument(
        "--source-projection-primary",
        choices=["canonical", "scored"],
        default="canonical",
    )
    cone.add_argument(
        "--dasl-distribution",
        choices=["full", "encoding-prior", "monster-primes", "attack-triple"],
        default="monster-primes",
    )
    cone.add_argument(
        "--eigen-source",
        choices=["trace", "jmd", "dasl", "hybrid"],
        default="trace",
    )
    cone.add_argument("--eigen-threshold", type=float, default=(1.0 / 3.0))
    cone.add_argument("--json", action="store_true")
    cone.set_defaults(func=cone_mode)

    return parser


def main(argv: Sequence[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    if getattr(args, "mode", None) == "cone" and args.preset == "dashifine-closure-embedding":
        args.default_group = args.default_group or args.monster_label
        args.name_column = "label"
        args.time_column = "iter"
        args.embedding_columns = ["v_pnorm", "v_dnorm", "v_depth", "v_arrow"]
        args.structural_columns = ["v_pnorm", "v_dnorm", "v_depth"]
        args.arrow_column = "v_arrow"
        args.arrow_direction = "nonincreasing"
        args.log_columns = []
        args.nonincreasing_columns = ["v_dnorm", "v_arrow"]
        args.energy_columns = ["v_pnorm", "v_dnorm", "v_arrow"]
        args.energy_weights = [1.0, 1.0, 0.1]
    if getattr(args, "mode", None) == "cone" and args.arrow_profile:
        args.arrow_eps = ARROW_PROFILES[args.arrow_profile]
    return args.func(args)


if __name__ == "__main__":
    raise SystemExit(main())
