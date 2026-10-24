"""Source-gated report-level temporal motif evaluator (synthetic tests only).

Does not infer temporal order from Erowid static category frequencies.
No external-agent ontology inference; neither rights nor data are supplied.
"""
import argparse
import json
from collections import Counter
from fractions import Fraction
from pathlib import Path

SCHEMA = "dashi-dmt-temporal-motifs-v1"


def validate(data):
    if data.get("schema") != SCHEMA or data.get("observation_unit") != "report":
        raise ValueError("Requires typed report-level observation schema")
    governance = data.get("governance", {})
    if governance.get("written_permission_reference") in (None, "", "unverified"):
        raise ValueError("Written corpus permission review reference required")
    if governance.get("chronology_method_reference") in (None, "", "unverified"):
        raise ValueError("Chronology protocol reference required")
    reports = data.get("reports")
    if not isinstance(reports, list) or len(reports) < 2:
        raise ValueError("At least two report records required")
    seen = set()
    for report in reports:
        identity = report.get("report_id")
        if not isinstance(identity, str) or not identity or identity in seen:
            raise ValueError("Missing/duplicate report identity")
        seen.add(identity)
        if report.get("chronology_verified") is not True:
            raise ValueError("Unverified chronology")
        events = report.get("events")
        if not isinstance(events, list) or len(events) < 2:
            raise ValueError("Two ordered events needed")
        if any(not isinstance(e.get("ordinal"), int)
               or isinstance(e.get("ordinal"), bool)
               or not isinstance(e.get("motif"), str)
               or not e["motif"] for e in events):
            raise ValueError("Malformed ordinal or motif")
        ordinals = [e["ordinal"] for e in events]
        if ordinals != sorted(set(ordinals)):
            raise ValueError("Unordered or duplicate positions")
    return reports


def transitions(report):
    motifs = [e["motif"] for e in report["events"]]
    return list(zip(motifs, motifs[1:]))


def _product(values):
    result = Fraction(1)
    for value in values:
        result *= value
    return result


def evaluate(data):
    reports = validate(data)
    labels = sorted({e["motif"] for r in reports for e in r["events"]})
    output = []
    for held in reports:
        training = [r for r in reports if r["report_id"] != held["report_id"]]
        edges = Counter(edge for r in training for edge in transitions(r))
        predecessors = Counter()
        successors = Counter()
        for (a, b), count in edges.items():
            predecessors[a] += count
            successors[b] += count
        total = sum(successors.values())
        k = len(labels)
        ratios = []
        for a, b in transitions(held):
            p_temporal = Fraction(edges[a, b] + 1, predecessors[a] + k)
            p_static = Fraction(successors[b] + 1, total + k)
            ratios.append(p_temporal / p_static)
        output.append({"report_id": held["report_id"],
                       "transitions": len(ratios),
                       "likelihood_ratio_exact": str(_product(ratios))})
    return {"schema": "dashi-dmt-temporal-motif-evaluation-v1",
            "method": "report-exclusive leave-one-report-out",
            "report_count": len(reports), "motif_count": len(labels),
            "report_results": output,
            "measured_neural_mechanism": False,
            "independent_external_agent_inferred": False,
            "same_participant_cross_study_join": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source_json", type=Path)
    args = parser.parse_args()
    print(json.dumps(evaluate(json.loads(args.source_json.read_text(encoding="utf8"))), indent=2))


if __name__ == "__main__":
    main()
