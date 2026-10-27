from __future__ import annotations

from collections import defaultdict
from typing import Iterable

from .discovery import round_family


def _symbol_map(module: dict) -> dict[str, str]:
    result: dict[str, str] = {}
    module_name = str(module.get("module_name", ""))
    prefix = module_name + "." if module_name else ""
    for symbol in module.get("symbols", ()):
        name = symbol.get("name") or symbol.get("qualified_name")
        if not name:
            continue
        name = str(name)
        if prefix and name.startswith(prefix):
            name = name[len(prefix):]
        result[name] = str(symbol.get("signature_sha256", ""))
    return result


def compute_round_lineage(modules: Iterable[dict]) -> dict:
    grouped: dict[str, list[tuple[int, dict]]] = defaultdict(list)
    for module in modules:
        module_name = str(module.get("module_name", ""))
        family, number = round_family(module_name)
        if family is None or number is None:
            continue
        grouped[family].append((number, module))

    families = []
    for family_name in sorted(grouped):
        ordered = sorted(grouped[family_name], key=lambda item: item[0])
        transitions = []
        for (left_no, left), (right_no, right) in zip(ordered, ordered[1:]):
            left_symbols = _symbol_map(left)
            right_symbols = _symbol_map(right)
            left_names = set(left_symbols)
            right_names = set(right_symbols)
            added_names = right_names - left_names
            removed_names = left_names - right_names
            common = left_names & right_names
            changed = {
                name
                for name in common
                if left_symbols[name] != right_symbols[name]
            }
            unchanged = common - changed
            denominator = max(1, len(right_symbols))
            novelty = (len(added_names) + len(changed)) / denominator
            # Compute both ratios from integer counts.  Using 1.0 - novelty
            # produces a different IEEE float for values such as 1/3.
            noise = len(unchanged) / denominator
            transitions.append(
                {
                    "from_round": left_no,
                    "to_round": right_no,
                    "added": len(added_names),
                    "removed": len(removed_names),
                    "signature_changed": len(changed),
                    "unchanged": len(unchanged),
                    "novelty_ratio": novelty,
                    "snapshot_noise_ratio": noise,
                }
            )
        families.append(
            {
                "family": family_name,
                "rounds": [number for number, _ in ordered],
                "module_count": len(ordered),
                "transitions": transitions,
            }
        )
    return {"families": families}
