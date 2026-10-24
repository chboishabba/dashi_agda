#!/usr/bin/env python3
"""Case-specific 2013/2024 published Rodin table/citation audit.

This is bibliographic and arithmetic validation, NOT a magnetometer replay,
proof of data reuse or accusation of author misconduct. Original authors
retain their original measurements and interpretations.
"""
from __future__ import annotations
import argparse
import csv
import json
from decimal import Decimal, InvalidOperation
from pathlib import Path

DEFAULT = Path(__file__).resolve().parents[1] / 'docs' / 'research' / 'psychotronics-phase1-rodin-field-table-concordance-20261025.csv'
EXPECTED = (('1.60', '100', '4.13'), ('1.25', '800', '3.05'), ('0.60', '2450', '1.16'))
CITED_ORIGINALS = {
    14: ('Rodin & Volk', '2010'),
    13: ('Maldonado-Moreles et al.', '2021'),
    23: ('Aparicio-Bautista et al.', '2022'),
}
TARGET_2013_DOI = '10.1063/1.4819796'


def audit(path: Path = DEFAULT, original_2024_bibliography: dict | None = None) -> dict:
    """Verify only source-recorded printed values and bounded reference claims."""
    with path.open(newline='', encoding='utf-8') as handle:
        rows = list(csv.DictReader(handle))
    if len(rows) != len(EXPECTED):
        raise ValueError('expected exactly three original printed value rows')
    for row, (current, freq, observed) in zip(rows, EXPECTED):
        if not {'current_a', 'perez_2013_frequency_hz', 'perez_2013_experiment_mt',
                'ramirez_galindo_2024_experiment_mt', 'perez_2013_theory_mt',
                'ramirez_galindo_2024_theory_mt', 'ramirez_galindo_2024_simulation_mt',
                'reused_raw_trace_proved'}.issubset(row):
            raise ValueError('missing original bibliographic measurement field')
        try:
            actual = tuple(Decimal(row[k]) for k in
                ('current_a','perez_2013_frequency_hz','perez_2013_experiment_mt','ramirez_galindo_2024_experiment_mt'))
        except (InvalidOperation, ValueError) as exc:
            raise ValueError('invalid printed physical units/value') from exc
        if actual != (Decimal(current), Decimal(freq), Decimal(observed), Decimal(observed)):
            raise ValueError('2013/2024 printed field-value concordance differs')
        if row['reused_raw_trace_proved'].lower() != 'false':
            raise ValueError('rounded values do not identify raw traces')
        if Decimal(row['perez_2013_theory_mt']) == Decimal(row['ramirez_galindo_2024_theory_mt']):
            raise ValueError('distinct original theoretical columns were collapsed')
    # Original bibliography checked visually at the publisher's printed pp6-7.
    # It is optional as an INPUT to let callers provide an independently typed
    # canonical reference index, rather than falsely deriving bibliography from
    # the 3-row measurement CSV.
    refs = original_2024_bibliography
    if refs is not None:
        if set(refs) != set(range(1,25)):
            raise ValueError('2024 bibliography must include original 24 numbered items')
        if TARGET_2013_DOI in ' '.join(str(s).lower() for s in refs.values()):
            raise ValueError('contradicts inspected original 2024 bibliography noncitation')
        for number, (source, year) in CITED_ORIGINALS.items():
            if source.lower() not in str(refs[number]).lower() or year not in str(refs[number]):
                raise ValueError('lost original #13/#14/#23 bibliography distinction')
    return {
        'status': 'PUBLISHED_RECORDS_CONCORDANT_INDEPENDENCE_UNRESOLVED',
        'original_2024_reference_count_visually_inspected': 24,
        'explicit_2013_RSI_DOI_in_2024_references': False,
        '2013_RSI_DOI_original': TARGET_2013_DOI,
        'source_2024_reference_list_checked_from_input': refs is not None,
        'same_reported_current_field_pairs': len(rows),
        '2013_printed_frequencies_hz': [int(x[1]) for x in EXPECTED],
        '2024_theory_model_steady_state_as_printed': True,
        '2024_physical_sensor_acquisition_frequency_derived_from_steady_state_model': False,
        '2013_2024_raw_session_identity': 'UNRESOLVED',
        'misconduct_or_plagiarism_established': False,
        'novel_non_Maxwell_physics_observed': False,
    }


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument('--csv', type=Path, default=DEFAULT)
    args = p.parse_args()
    print(json.dumps(audit(args.csv), sort_keys=True, indent=2))


if __name__ == '__main__':
    main()
