from __future__ import annotations

import json


RETRIEVED = "2026-09-16"


def _node(
    sequence_id: str,
    *,
    title: str,
    class_label: str | None = None,
    q0: int | None = None,
    positive_coefficients: dict[int, int] | None = None,
    selected_terms: dict[int, int] | None = None,
    selected_values: set[int] | None = None,
    formula: str | None = None,
    authority: str,
    url: str,
    notes: str,
) -> dict[str, object]:
    return {
        "sequence_id": sequence_id,
        "title": title,
        "class_label": class_label,
        "q0": q0,
        "positive_coefficients": positive_coefficients or {},
        "selected_terms": selected_terms or {},
        "selected_values": selected_values or set(),
        "formula": formula,
        "authority": authority,
        "url": url,
        "retrieved": RETRIEVED,
        "notes": notes,
    }


SEQUENCES: dict[str, dict[str, object]] = {
    "A005052": _node(
        "A005052",
        title="a(n) = 10*3^n",
        selected_terms={2: 90, 8: 65610, 9: 196830},
        formula="10*3^n",
        authority="numerical-navigation",
        url="https://oeis.org/A005052",
        notes=(
            "Exact numerical ladder used for 90 -> 65610 -> 196830 discovery. "
            "Does not identify Monster carriers or representations."
        ),
    ),
    "A025616": _node(
        "A025616",
        title="Numbers of form 3^i*10^j, with i,j >= 0",
        selected_values={90, 729, 65610, 196830},
        formula="3^i*10^j",
        authority="numerical-navigation",
        url="https://oeis.org/A025616",
        notes=(
            "Broader multiplicative parent lattice. The key Monster369 arithmetic "
            "coordinates are 90=3^2*10, 729=3^6, 65610=3^8*10, "
            "196830=3^9*10. Arithmetic structure only."
        ),
    ),
    "A058678": _node(
        "A058678",
        title="McKay-Thompson series of class 42d for Monster",
        class_label="42d",
        selected_values={17496},
        formula="q^(1/2)*eta(q^3)*eta(q^7)/(eta(q)*eta(q^21))",
        authority="source-navigation",
        url="https://oeis.org/A058678",
        notes=(
            "Monster 42d McKay-Thompson source coordinate. The documented coefficient "
            "17496 is retained as a positive bridge target against the independently "
            "source-paid N(3B) restriction degree 2*729*12; no same-object bridge is implied."
        ),
    ),
    "A007255": _node(
        "A007255",
        title="McKay-Thompson series of class 6B for Monster",
        class_label="6B",
        q0=0,
        positive_coefficients={1: 78, 2: 364, 3: 1365, 4: 4380, 5: 12520, 6: 32772},
        authority="source-navigation",
        url="https://oeis.org/A007255",
        notes=(
            "Normalized 6B manifestation. OEIS cross-references A045485/A121665 "
            "and states agreement apart from n=0."
        ),
    ),
    "A045485": _node(
        "A045485",
        title="McKay-Thompson series of class 6B for Monster with a(0)=7",
        class_label="6B",
        q0=7,
        positive_coefficients={1: 78, 2: 364, 3: 1365, 4: 4380, 5: 12520, 6: 32772},
        authority="source-navigation",
        url="https://oeis.org/A045485",
        notes="Alternate 6B q^0 normalization; positive-degree prefix agrees through q^6.",
    ),
    "A121665": _node(
        "A121665",
        title="McKay-Thompson series of class 6B for Monster with a(0)=12",
        class_label="6B",
        q0=12,
        positive_coefficients={1: 78, 2: 364, 3: 1365, 4: 4380, 5: 12520, 6: 32772},
        authority="source-navigation",
        url="https://oeis.org/A121665",
        notes="Alternate 6B q^0 normalization; positive-degree prefix agrees through q^6.",
    ),
    "A007244": _node(
        "A007244",
        title="McKay-Thompson series of class 3B for the Monster group",
        class_label="3B",
        q0=0,
        positive_coefficients={1: 54, 2: -76, 3: -243, 4: 1188, 5: -1384, 6: -2916},
        authority="source-navigation",
        url="https://oeis.org/A007244",
        notes="3B graded-trace source coordinate; class power/action authority remains external.",
    ),
    "A007246": _node(
        "A007246",
        title="McKay-Thompson series of class 2B for the Monster group",
        class_label="2B",
        q0=0,
        positive_coefficients={1: 276, 2: -2048, 3: 11202, 4: -49152, 5: 184024},
        authority="source-navigation",
        url="https://oeis.org/A007246",
        notes="2B graded-trace source coordinate; class power/action authority remains external.",
    ),
    "A014708": _node(
        "A014708",
        title="McKay-Thompson series of class 1A / J=j-744",
        class_label="1A",
        q0=0,
        positive_coefficients={1: 196884, 2: 21493760, 3: 864299970},
        authority="source-navigation",
        url="https://oeis.org/A014708",
        notes="Moonshine/J coefficient source coordinate; not a VOA same-object receipt.",
    ),
    "A001379": _node(
        "A001379",
        title="Degrees of irreducible representations of Monster group M",
        selected_terms={1: 1, 2: 196883},
        authority="source-navigation",
        url="https://oeis.org/A001379",
        notes="Monster irreducible-degree navigation; does not construct a chosen representation.",
    ),
    "A309510": _node(
        "A309510",
        title="Divisors of 196883",
        selected_terms={1: 1, 2: 47, 3: 59, 4: 71, 8: 196883},
        authority="numerical-navigation",
        url="https://oeis.org/A309510",
        notes="Arithmetic/Ogg-prime navigation; does not create Monster representation semantics.",
    ),
}


RELATIONS: dict[str, dict[str, object]] = {
    "6b-normalization-positive-degree-agreement": {
        "sources": ["A007255", "A045485", "A121665"],
        "scope": "positive coefficients q^1 through q^6",
        "paid": True,
        "same_object_paid": False,
    },
    "a005052-heisenberg-ladder": {
        "sources": ["A005052"],
        "observed": "90 * 729 = 65610 and 3 * 65610 = 196830",
        "paid": True,
        "same_object_paid": False,
    },
    "a025616-parent-lattice": {
        "sources": ["A025616", "A005052"],
        "observed": (
            "90=3^2*10, 729=3^6, 65610=3^8*10, 196830=3^9*10; "
            "the 90*729=65610 lift is exponent addition (2,1)+(6,0)=(8,1)"
        ),
        "paid": True,
        "same_object_paid": False,
    },
    "42d-17496-to-n3b-restriction": {
        "sources": ["A058678"],
        "observed": (
            "Monster 42d McKay-Thompson coefficient 17496 equals the independently "
            "source-paid N(3B) restriction constituent degree 2*729*12"
        ),
        "paid": True,
        "same_object_paid": False,
    },
    "6b-q6-to-c6-spectrum-32772": {
        "sources": ["A007255", "A045485", "A121665"],
        "observed": "normalization-stable q^6 coefficient 32772 equals independent C6 m1=m5=32772",
        "paid": True,
        "same_object_paid": False,
    },
    "monster-power-family-weight-two-traces": {
        "sources": ["A007246", "A007244", "A007255", "A014708"],
        "observed": "2B=276, 3B=54, 6B=78, 1A=196884 at q^1",
        "paid": True,
        "class_power_map_paid_by_oeis": False,
    },
}


def build_report() -> dict[str, object]:
    return {
        "schema": "monster369-oeis-acquisition-snapshot-v3",
        "retrieved": RETRIEVED,
        "sequence_count": len(SEQUENCES),
        "sequences": SEQUENCES,
        "relations": RELATIONS,
        "positive_bridge_candidates": {
            "a005052-heisenberg-ladder": True,
            "a025616-parent-lattice": True,
            "6b-q6-to-c6-spectrum-32772": True,
            "17496-42d-to-n3b-restriction": True,
        },
        "authority": {
            "oeis_snapshot_creates_same_object": False,
            "oeis_snapshot_creates_monster_action": False,
            "positive_bridge_signal_creates_theorem": False,
        },
    }


def main() -> int:
    def normalize(value: object) -> object:
        if isinstance(value, set):
            return sorted(value)
        if isinstance(value, dict):
            return {key: normalize(item) for key, item in value.items()}
        if isinstance(value, list):
            return [normalize(item) for item in value]
        return value

    print(json.dumps(normalize(build_report()), indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
